# 071 验证编译脚本（绕开 lake 的 git manifest 网络校验，直接 lean.exe + LEAN_PATH）
# 用法: powershell -File build071.ps1 [--timeout 秒]
param(
  [int]$TimeSec = 3000
)
$ErrorActionPreference = "Continue"
$base = "I:\research\justin-sun-prize\work\jsp-071\verify-current"
$lean = "I:\Lean4\.elan\bin\lean.exe"
Set-Location $base

# 收集所有包的 olean 目录
$paths = @("$base\olean")
Get-ChildItem "$base\.lake\packages" -Directory | ForEach-Object {
  $p = "$($_.FullName)\.lake\build\lib\lean"
  if (Test-Path $p) { $paths += $p }
}
$env:LEAN_PATH = ($paths -join ";")
Write-Host "LEAN_PATH entries: $($paths.Count)"

# 编译顺序：Erdos862 -> Erdos42(引用) -> Erdos43
$targets = @(
  @{ src = "ErdosProblems\Erdos862.lean"; out = "olean\ErdosProblems\Erdos862.olean" },
  @{ src = "ErdosProblems\Erdos43.lean";  out = "olean\ErdosProblems\Erdos43.olean" }
)
$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($t in $targets) {
  Write-Host "==> compiling $($t.src)"
  & $lean -o $t.out $t.src 2>&1 | Select-Object -Last 20
  if ($LASTEXITCODE -ne 0) { Write-Host "FAILED: $($t.src)"; break }
  Write-Host "    OK: $($t.src) @ $([math]::Round($sw.Elapsed.TotalSeconds,1)) s"
}
$sw.Stop()
Write-Host "total: $([math]::Round($sw.Elapsed.TotalSeconds,1)) s"
