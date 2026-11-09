param(
  [int]$Runs = 100,
  [int]$RegionIterations = 5000,
  [string]$BaselineExe = '',
  [string]$OutDir = 'benchmark_results'
)
$ErrorActionPreference = 'Stop'
if ($Runs -lt 1 -or $Runs -gt 1000) { throw 'Runs must be 1..1000' }
if ($RegionIterations -lt 1 -or $RegionIterations -gt 100000) { throw 'RegionIterations must be 1..100000' }
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$exe = Join-Path $root 'target\release\qrust.exe'
if (!(Test-Path $exe)) { throw "Missing $exe; run cargo build --release" }
$out = Join-Path $root $OutDir
New-Item -ItemType Directory -Force $out | Out-Null
$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$report = Join-Path $out "benchmark-066-$stamp.txt"
function Run([string]$name,[string]$bin,[string[]]$argv) {
  "`n=== $name ===" | Tee-Object -FilePath $report -Append
  $result = & $bin @argv 2>&1 | Out-String
  $result | Tee-Object -FilePath $report -Append
  if ($LASTEXITCODE -ne 0) { throw "$name failed (exit $LASTEXITCODE)" }
}
$region = Join-Path $root 'benchmark_fixtures\reference_nll_0523.qr'
$branch = Join-Path $root 'benchmark_fixtures\reference_cfg_branch_0523.qr'
$stress = Join-Path $root 'benchmark_fixtures\function_stress.qr'
Run '0.6.6 region NLL (no file I/O)' $exe @('bench-regions',$region,$RegionIterations)
Run '0.6.6 CFG branch (no file I/O)' $exe @('bench-regions',$branch,$RegionIterations)
Run '0.6.6 function stress (no file I/O)' $exe @('bench-regions',$stress,$RegionIterations)
Run '0.6.6 persistent QASM end-to-end' $exe @('bench-e2e',$stress,$Runs,'--persistent')
Run '0.6.6 file I/O phases' $exe @('bench-io-phases',$stress,$Runs)
if ($BaselineExe) {
  if (!(Test-Path $BaselineExe)) { throw "Missing baseline executable $BaselineExe" }
  Run '0.6.5 baseline NLL' $BaselineExe @('bench-regions',$region,$RegionIterations)
  Run '0.6.5 baseline CFG branch' $BaselineExe @('bench-regions',$branch,$RegionIterations)
  Run '0.6.5 baseline function stress' $BaselineExe @('bench-regions',$stress,$RegionIterations)
}
$size = [long](Get-Item $exe).Length
"`n0.6.6 release executable: $size bytes ($([math]::Round($size/1MB,5)) MiB)" |
  Tee-Object -FilePath $report -Append
if ($BaselineExe) {
  $baselineSize = [long](Get-Item $BaselineExe).Length
  "0.6.5 baseline executable: $baselineSize bytes; delta $($size-$baselineSize) bytes" |
    Tee-Object -FilePath $report -Append
}
Write-Host "Saved to: $report"
