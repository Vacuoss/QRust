$ErrorActionPreference = 'Stop'
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.8 test regression failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.8 release build failed; benchmarks will not run' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
if (-not (Test-Path $exe)) { throw 'Missing freshly compiled release binary' }
foreach ($fixture in @('reference_nll_0523.qr', 'reference_cfg_branch_0523.qr', 'function_stress.qr')) {
    & $exe bench-regions (Join-Path 'benchmark_fixtures' $fixture) 5000
    if ($LASTEXITCODE -ne 0) { throw "Region analysis failed: $fixture" }
}
& $exe bench-e2e 'benchmark_fixtures\function_stress.qr' 100 --persistent
if ($LASTEXITCODE -ne 0) { throw 'Persistent I/O comparison failed' }
Write-Host "QRust 0.6.8 release bytes: $((Get-Item $exe).Length)"
