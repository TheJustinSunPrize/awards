param([string]$LeanBin = (Join-Path $PSScriptRoot '..\toolchain\lean-4.33.1-windows\bin'))

$ErrorActionPreference = 'Stop'
$taskPreviousPath = $env:PATH
$taskPreviousThreads = $env:LEAN_NUM_THREADS
$taskLogDir = Join-Path $PSScriptRoot 'verification'
function Write-TaskText([string]$Path, $Lines) {
    $taskText = ((@($Lines) | ForEach-Object { "$_" }) -join "`n").Replace("`r`n", "`n") + "`n"
    [System.IO.File]::WriteAllText($Path, $taskText, [System.Text.UTF8Encoding]::new($false))
}
New-Item -ItemType Directory -Path $taskLogDir -Force | Out-Null
Push-Location $PSScriptRoot
try {
    if ($LeanBin -and (Test-Path -LiteralPath $LeanBin)) {
        $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + ';' + $env:PATH
    }
    $env:LEAN_NUM_THREADS = '1'
    $taskBuild = & lake --wfail build Cerny 2>&1
    $taskBuildExit = $LASTEXITCODE
    Write-TaskText (Join-Path $taskLogDir 'build.log') $taskBuild
    $taskBuild | Write-Output
    if ($taskBuildExit -ne 0) { throw "Build failed: $taskBuildExit" }

    $taskAudit = & lake env lean -DwarningAsError=true Audit.lean 2>&1
    $taskAuditExit = $LASTEXITCODE
    Write-TaskText (Join-Path $taskLogDir 'axioms.log') $taskAudit
    $taskAudit | Write-Output
    if ($taskAuditExit -ne 0) { throw "Axiom audit failed: $taskAuditExit" }
    $taskAxiomLines = @($taskAudit | Where-Object { "$_" -match 'depends on axioms:' })
    if ($taskAxiomLines.Count -ne 10) { throw 'Expected 10 axiom reports.' }
    foreach ($taskLine in $taskAxiomLines) {
        if ("$taskLine" -notmatch "^'Cerny\.[A-Za-z_]+'.*depends on axioms: \[([^\]]*)\]$") {
            throw "Unrecognized axiom report: $taskLine"
        }
        foreach ($taskAxiom in ($Matches[1] -split ', ')) {
            if ($taskAxiom -notin @('propext','Classical.choice','Quot.sound')) {
                throw "Unexpected axiom: $taskAxiom"
            }
        }
    }
    if (Select-String -LiteralPath 'Cerny.lean' -Pattern '\bsorry\b|\badmit\b|\baxiom\b|native_decide|ofReduceBool|trustCompiler|\bunsafe\b') {
        throw 'Unexpected proof escape in Cerny.lean.'
    }

    $taskReplay = & lake env leanchecker --verbose Cerny 2>&1
    $taskReplayExit = $LASTEXITCODE
    Write-TaskText (Join-Path $taskLogDir 'replay.log') $taskReplay
    $taskReplay | Write-Output
    if ($taskReplayExit -ne 0) { throw "Kernel replay failed: $taskReplayExit" }
    $taskReplayedModules = @($taskReplay | Where-Object { "$_" -match '^replaying ' } | ForEach-Object { "$_".Substring(10).Trim() })
    if ($taskReplayedModules.Count -ne 1 -or $taskReplayedModules[0] -ne 'Cerny') {
        throw 'Kernel replay did not cover exactly the local Cerny module.'
    }

    $taskFiles = '.gitattributes','.gitignore','LICENSE','Cerny.lean','Audit.lean','lean-toolchain','lakefile.toml','lake-manifest.json','README.md','PROOF.md','SOURCE_COMPARISON.md','statement-review.md','verify.ps1'
    $taskHashes = @(Get-Item -LiteralPath $taskFiles | Sort-Object FullName | ForEach-Object {
        [ordered]@{
            path = $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/')
            sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $_.FullName).Hash.ToLowerInvariant()
            bytes = $_.Length
        }
    })
    Write-TaskText (Join-Path $taskLogDir 'files-sha256.json') ($taskHashes | ConvertTo-Json)
    $taskResult = [ordered]@{
        checkedAt = (Get-Date -Format o)
        buildExitCode = $taskBuildExit
        auditExitCode = $taskAuditExit
        replayExitCode = $taskReplayExit
        auditedDeclarations = $taskAxiomLines.Count
        replayedModules = $taskReplayedModules
        leanVersion = (& lean --version | Out-String).Trim()
        mathlibRevision = (& git -C .lake/packages/mathlib rev-parse HEAD | Out-String).Trim()
        leanNumThreads = 1
        trustBoundary = 'Official Lean elaborator and same-kernel leanchecker replay of local Cerny module. Imported Mathlib/package caches are trusted. No independent checker implementation or fresh replay of every import; no network isolation.'
    }
    Write-TaskText (Join-Path $taskLogDir 'result.json') ($taskResult | ConvertTo-Json -Depth 4)
} finally {
    $env:PATH = $taskPreviousPath
    $env:LEAN_NUM_THREADS = $taskPreviousThreads
    Pop-Location
}
