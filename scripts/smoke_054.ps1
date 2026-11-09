$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/function_stress.qr','examples/loop_indexed_053.qr','examples/loop_parametric_054.qr','examples/runtime_while.qr')) {
    & $exe check $file
    if ($LASTEXITCODE -ne 0) { throw "check failed: $file" }
}
& $exe build examples/loop_parametric_054.qr
if ($LASTEXITCODE -ne 0) { throw 'QASM build failed' }
& $exe ir-stats examples/loop_parametric_054.qr
if ($LASTEXITCODE -ne 0) { throw 'IR stats failed' }
Write-Host 'QRust 0.5.4 smoke checks completed.'
