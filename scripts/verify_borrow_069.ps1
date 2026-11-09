$ErrorActionPreference = 'Stop'
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.9 tests failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.9 release build failed; refusing stale executable benchmark' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
if (-not (Test-Path $exe)) { throw 'Missing freshly compiled release executable' }
foreach ($fixture in @('reference_nll_0523.qr', 'reference_cfg_branch_0523.qr', 'function_stress.qr')) {
    & $exe bench-regions (Join-Path 'benchmark_fixtures' $fixture) 5000
    if ($LASTEXITCODE -ne 0) { throw "Region analysis failed: $fixture" }
}
& $exe bench-e2e 'benchmark_fixtures\function_stress.qr' 100 --persistent
if ($LASTEXITCODE -ne 0) { throw 'Persistent writer benchmark failed' }
Write-Host "QRust 0.6.9 release bytes: $((Get-Item $exe).Length)"
