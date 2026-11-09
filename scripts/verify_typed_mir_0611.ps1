param([int]$RegionIterations=5000)
$ErrorActionPreference='Stop'
$root=Split-Path -Parent $PSScriptRoot
Push-Location $root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'Typed MIR 0.6.11 unit tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'Typed MIR 0.6.11 release build failed' }
    $exe=Join-Path $root 'target\release\qrust.exe'
    if (-not (Test-Path $exe)) { throw 'Release executable missing' }
    foreach ($fixture in @('reference_nll_0523.qr','reference_cfg_branch_0523.qr','function_stress.qr')) {
        & $exe bench-regions (Join-Path 'benchmark_fixtures' $fixture) $RegionIterations
        if ($LASTEXITCODE -ne 0) { throw "Region benchmark failed: $fixture" }
    }
    & $exe bench-e2e 'benchmark_fixtures/function_stress.qr' 100 --persistent
    if ($LASTEXITCODE -ne 0) { throw 'Persistent benchmark failed' }
    Write-Host "QRust 0.6.11 executable size: $((Get-Item $exe).Length) bytes"
} finally { Pop-Location }
