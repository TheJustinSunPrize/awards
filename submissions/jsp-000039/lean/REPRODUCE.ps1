param([switch]$SkipCache)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
if (Test-Path variable:PSNativeCommandUseErrorActionPreference) {
    $PSNativeCommandUseErrorActionPreference = $false
}

function Invoke-Logged {
    param([string]$Program, [string[]]$Arguments, [string]$LogName)
    $output = @(& $Program @Arguments 2>&1)
    $code = $LASTEXITCODE
    $output | ForEach-Object { $_.ToString() } |
        Set-Content -LiteralPath (Join-Path $logRoot $LogName) -Encoding utf8
    $output | ForEach-Object { Write-Host $_ }
    if ($code -ne 0) { throw "$Program failed with exit code $code" }
}

Push-Location $PSScriptRoot
try {
    $logRoot = Join-Path $PSScriptRoot 'reproduction'
    New-Item -ItemType Directory -Force -Path $logRoot | Out-Null
    $sources = @(
        Get-Item 'DGGCounterexample.lean','Audit.lean'
        Get-ChildItem 'DGGCounterexample' -Filter '*.lean' -File -Recurse
    )
    $hits = @($sources | Select-String -Pattern '\b(sorry|admit|axiom|native_decide)\b')
    if ($hits.Count -gt 0) { throw 'Forbidden source construct found.' }
    'No forbidden source constructs found in project Lean sources.' |
        Set-Content (Join-Path $logRoot 'source-scan.log') -Encoding utf8

    $manifestBefore = (Get-FileHash 'lake-manifest.json' -Algorithm SHA256).Hash
    Invoke-Logged -Program 'lean' -Arguments @('--version') -LogName 'lean-version.log'
    Invoke-Logged -Program 'lake' -Arguments @('--version') -LogName 'lake-version.log'
    if (-not $SkipCache) {
        Invoke-Logged -Program 'lake' -Arguments @('exe','cache','get') -LogName 'cache.log'
    }
    Invoke-Logged -Program 'lake' -Arguments @('build') -LogName 'lean-build.log'
    Invoke-Logged -Program 'lake' -Arguments @('env','lean','Audit.lean') -LogName 'axioms.log'

    $audit = Get-Content (Join-Path $logRoot 'axioms.log') -Raw
    $reports = [regex]::Matches($audit, "'DGG\.[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    if ($reports.Count -ne 21) { throw 'Expected 21 theorem axiom reports.' }
    foreach ($report in $reports) {
        foreach ($name in ($report.Groups[1].Value -split ',')) {
            if ($name.Trim() -and $name.Trim() -notin @('propext','Classical.choice','Quot.sound')) {
                throw "Unapproved axiom dependency: $($name.Trim())"
            }
        }
    }
    if ($audit -match 'sorryAx') { throw 'Unproved theorem dependency detected.' }
    if ((Get-FileHash 'lake-manifest.json' -Algorithm SHA256).Hash -ne $manifestBefore) {
        throw 'The dependency manifest changed during reproduction.'
    }
    'PASS: build, source scan, 21 transitive axiom reports, unchanged manifest.' |
        Set-Content (Join-Path $logRoot 'result.log') -Encoding utf8
    Write-Host 'PASS: build, source scan, 21 transitive axiom reports, unchanged manifest.'
} finally {
    Pop-Location
}
