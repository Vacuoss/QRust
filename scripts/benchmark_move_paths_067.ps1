param([int]$RegionIterations=5000, [int]$EndToEndRuns=100)
$ErrorActionPreference = "Stop"
# Never benchmark a stale 0.6.6 executable when the current source fails
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.7 release build failed. Benchmark aborted to prevent stale measurements.' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
if (-not (Test-Path $exe)) { throw 'Build QRust with cargo build --release first.' }
$exe = (Resolve-Path $exe).Path
$size=(Get-Item $exe).Length
Write-Host "QRust 0.6.7 actual release executable: $size bytes"
foreach($fixture in @('reference_nll_0523.qr','reference_cfg_branch_0523.qr','function_stress.qr')) {
  $f="benchmark_fixtures\$fixture"
  Write-Host "== Region-only $fixture =="
  & $exe bench-regions $f $RegionIterations
  if ($LASTEXITCODE -ne 0) { throw "Region benchmark failed: $fixture" }
}
Write-Host '== Persistent QASM end-to-end =='
& $exe bench-e2e 'benchmark_fixtures\function_stress.qr' $EndToEndRuns --persistent
if ($LASTEXITCODE -ne 0) { throw 'Persistent benchmark failed.' }
