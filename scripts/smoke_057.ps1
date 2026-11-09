$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'cargo build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
& $exe check examples/loop_indexed_053.qr
if ($LASTEXITCODE -ne 0) { throw 'loop validation failed' }
& $exe bench-e2e examples/function_stress.qr 2
if ($LASTEXITCODE -ne 0) { throw 'end-to-end benchmark failed' }
& $exe bench-stress 10000
if ($LASTEXITCODE -ne 0) { throw '10K stress check failed' }
Write-Host 'QRust 0.5.7 smoke checks completed.'
