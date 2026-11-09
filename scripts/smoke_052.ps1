$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'cargo release build failed' }
& .\target\release\qrust.exe build examples/runtime_while.qr
if ($LASTEXITCODE -ne 0) { throw 'runtime_while build failed' }
$qasm = Get-Content examples/runtime_while.qasm -Raw
if (-not $qasm.Contains('while (c[0] == 1) {')) { throw 'missing runtime while in QASM' }
& .\target\release\qrust.exe check examples/runtime_feedback_branches.qr
if ($LASTEXITCODE -ne 0) { throw 'nested feedback branches invalid' }
& .\target\release\qrust.exe check examples/runtime_feedback_invalid.qr
if ($LASTEXITCODE -eq 0) { throw 'unsafe feedback accepted' }
& .\target\release\qrust.exe check examples/runtime_feedback_ownership_invalid.qr
if ($LASTEXITCODE -eq 0) { throw 'unsafe ownership accepted' }
Write-Host 'QRust 0.5.2 smoke checks completed.'
