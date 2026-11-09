$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'cargo build --release failed' }
& .\target\release\qrust.exe check examples/while_loop.qr
if ($LASTEXITCODE -ne 0) { throw 'while_loop.qr should compile' }
& .\target\release\qrust.exe build examples/while_loop.qr
if ($LASTEXITCODE -ne 0) { throw 'while_loop.qr should build' }
& .\target\release\qrust.exe check examples/while_invalid_feedback.qr
if ($LASTEXITCODE -eq 0) { throw 'measurement feedback must be rejected' }
& .\target\release\qrust.exe check examples/while_invalid_ownership.qr
if ($LASTEXITCODE -eq 0) { throw 'consumed Qubit must be rejected' }
& .\target\release\qrust.exe bench examples/core_gates.qr 100000
if ($LASTEXITCODE -ne 0) { throw 'core benchmark failed' }
& .\target\release\qrust.exe bench examples/function_stress.qr 1000 --detailed
if ($LASTEXITCODE -ne 0) { throw 'function benchmark failed' }
Write-Host 'All smoke checks completed.'
