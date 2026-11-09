$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/function_stress.qr','examples/runtime_while.qr','examples/loop_batch_053.qr')) {
    & $exe check $file
    if ($LASTEXITCODE -ne 0) { throw "check failed: $file" }
}
& $exe build examples/loop_batch_053.qr
if ($LASTEXITCODE -ne 0) { throw 'OpenQASM build failed' }
& $exe ir-stats examples/loop_batch_053.qr
if ($LASTEXITCODE -ne 0) { throw 'IR stats failed' }
Write-Host 'QRust 0.5.3 smoke checks completed.'
