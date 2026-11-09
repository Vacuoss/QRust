$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'cargo build --release failed' }
& .\target\release\qrust.exe check examples/runtime_if.qr
if ($LASTEXITCODE -ne 0) { throw 'runtime if example failed' }
& .\target\release\qrust.exe build examples/runtime_if.qr
if ($LASTEXITCODE -ne 0) { throw 'runtime if build failed' }
$qasm = Get-Content examples/runtime_if.qasm -Raw
if (-not $qasm.Contains('if (c[0] == 1) {')) { throw 'missing runtime branch in OpenQASM' }
& .\target\release\qrust.exe check examples/runtime_if_invalid.qr
if ($LASTEXITCODE -eq 0) { throw 'unsafe runtime branch was accepted' }
& .\target\release\qrust.exe check examples/while_invalid_feedback.qr
if ($LASTEXITCODE -eq 0) { throw 'dynamic while unexpectedly accepted' }
Write-Host 'QRust 0.5.1 smoke checks completed.'
