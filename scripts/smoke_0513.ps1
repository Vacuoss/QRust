$ErrorActionPreference = "Stop"
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw "cargo test failed" }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw "release build failed" }
    & target/release/qrust.exe capabilities
    if ($LASTEXITCODE -ne 0) { throw "capabilities failed" }
    & target/release/qrust.exe check examples/static_loop_control_0513.qr
    if ($LASTEXITCODE -ne 0) { throw "loop control compile check failed" }
    & target/release/qrust.exe build examples/static_loop_control_0513.qr --skip-unchanged
    if ($LASTEXITCODE -ne 0) { throw "OpenQASM build failed" }
    & target/release/qrust.exe build-qcu examples/static_loop_control_0513.qr
    if ($LASTEXITCODE -ne 0) { throw "QCU interchange build failed" }
    & target/release/qrust.exe check examples/static_loop_control_invalid_0513.qr
    if ($LASTEXITCODE -eq 0) { throw "invalid break unexpectedly compiled" }
    & target/release/qrust.exe check examples/rust_surface_0512.qr
    if ($LASTEXITCODE -ne 0) { throw "previous Rust surface regression" }
    Write-Host "QRust 0.5.13 Rust surface smoke completed."
} finally { Pop-Location }
