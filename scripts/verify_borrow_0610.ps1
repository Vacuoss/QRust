$ErrorActionPreference = 'Stop'
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.10 tests failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.10 release build failed; no benchmark with stale executable' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
if (-not (Test-Path $exe)) { throw 'QRust 0.6.10 release executable missing' }
foreach ($fixture in @('reference_nll_0523.qr', 'reference_cfg_branch_0523.qr', 'function_stress.qr')) {
    & $exe bench-regions (Join-Path 'benchmark_fixtures' $fixture) 5000
    if ($LASTEXITCODE -ne 0) { throw "Region analysis failed: $fixture" }
}
& $exe bench-e2e 'benchmark_fixtures\function_stress.qr' 100 --persistent
if ($LASTEXITCODE -ne 0) { throw 'Persistent end-to-end benchmark failed' }
Write-Host "QRust 0.6.10 release executable size: $((Get-Item $exe).Length) bytes"
