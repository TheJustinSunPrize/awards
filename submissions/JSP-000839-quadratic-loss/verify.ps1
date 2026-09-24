param([string]$LeanBin = (Join-Path $PSScriptRoot '..\toolchain\lean-4.33.1-windows\bin'))

$ErrorActionPreference = 'Stop'
$taskPreviousPath = $env:PATH
$taskPreviousThreads = $env:LEAN_NUM_THREADS
$taskLogDir = Join-Path $PSScriptRoot 'verification'
New-Item -ItemType Directory -Path $taskLogDir -Force | Out-Null
Push-Location $PSScriptRoot
try {
    if ($LeanBin -and (Test-Path -LiteralPath $LeanBin)) {
        $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + ';' + $env:PATH
    }
    $env:LEAN_NUM_THREADS = '1'
    $taskBuild = & lake --wfail build TrianglePacking 2>&1
    $taskBuildExit = $LASTEXITCODE
    $taskBuild | Set-Content -Encoding UTF8 -LiteralPath (Join-Path $taskLogDir 'build.log')
    $taskBuild | Write-Output
    if ($taskBuildExit -ne 0) { throw "Build failed: $taskBuildExit" }

    $taskAudit = & lake env lean -DwarningAsError=true Audit.lean 2>&1
    $taskAuditExit = $LASTEXITCODE
    $taskAudit | Set-Content -Encoding UTF8 -LiteralPath (Join-Path $taskLogDir 'axioms.log')
    $taskAudit | Write-Output
    if ($taskAuditExit -ne 0) { throw "Axiom audit failed: $taskAuditExit" }
    $taskAxiomLines = @($taskAudit | Where-Object { "$_" -match 'depends on axioms:' })
    if ($taskAxiomLines.Count -ne 18) { throw 'Expected 18 axiom reports.' }
    foreach ($taskLine in $taskAxiomLines) {
        if ("$taskLine" -notmatch 'depends on axioms: \[propext, Classical\.choice, Quot\.sound\]$') {
            throw "Unexpected axiom report: $taskLine"
        }
    }

    $taskSources = @(Get-ChildItem -LiteralPath 'TrianglePacking' -Filter '*.lean') + @(Get-Item -LiteralPath 'TrianglePacking.lean')
    foreach ($taskSource in $taskSources) {
        if (Select-String -LiteralPath $taskSource.FullName -Pattern '\bsorry\b|\baxiom\b|native_decide|ofReduceBool|trustCompiler|\bunsafe\b') {
            throw "Unexpected proof escape in $($taskSource.Name)"
        }
    }

    $taskReplay = & lake env leanchecker --verbose TrianglePacking 2>&1
    $taskReplayExit = $LASTEXITCODE
    $taskReplay | Set-Content -Encoding UTF8 -LiteralPath (Join-Path $taskLogDir 'replay.log')
    $taskReplay | Write-Output
    if ($taskReplayExit -ne 0) { throw "Kernel replay failed: $taskReplayExit" }
    $taskExpectedModules = @('TrianglePacking') + @(
        Get-ChildItem -LiteralPath 'TrianglePacking' -Filter '*.lean' | ForEach-Object { 'TrianglePacking.' + $_.BaseName }
    )
    $taskReplayedModules = @($taskReplay | Where-Object { "$_" -match '^replaying ' } | ForEach-Object { "$_".Substring(10).Trim() })
    if (Compare-Object ($taskExpectedModules | Sort-Object) ($taskReplayedModules | Sort-Object)) {
        throw 'Kernel replay did not cover exactly the local proof modules.'
    }

    $taskHashRecords = @($taskSources + @(Get-Item -LiteralPath 'Audit.lean','lean-toolchain','lakefile.toml','lake-manifest.json') | Sort-Object FullName | ForEach-Object {
        [ordered]@{
            path = $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/')
            sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $_.FullName).Hash.ToLowerInvariant()
            bytes = $_.Length
        }
    })
    $taskHashRecords | ConvertTo-Json | Set-Content -Encoding UTF8 -LiteralPath (Join-Path $taskLogDir 'files-sha256.json')
    [ordered]@{
        checkedAt = (Get-Date -Format o)
        buildExitCode = $taskBuildExit
        auditExitCode = $taskAuditExit
        replayExitCode = $taskReplayExit
        auditedDeclarations = $taskAxiomLines.Count
        replayedModules = $taskReplayedModules
        leanVersion = (& lean --version | Out-String).Trim()
        mathlibRevision = (& git -C .lake/packages/mathlib rev-parse HEAD | Out-String).Trim()
        leanNumThreads = 1
        trustBoundary = 'Official Lean elaborator and same-kernel leanchecker replay of local modules. Imported Mathlib/package caches are trusted. No independent checker implementation or fresh replay of every import; no network isolation.'
    } | ConvertTo-Json -Depth 4 | Set-Content -Encoding UTF8 -LiteralPath (Join-Path $taskLogDir 'result.json')
} finally {
    $env:PATH = $taskPreviousPath
    $env:LEAN_NUM_THREADS = $taskPreviousThreads
    Pop-Location
}
