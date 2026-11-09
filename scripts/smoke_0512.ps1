$ErrorActionPreference = "Stop"
cargo test
if ($LASTEXITCODE -ne 0) { throw "cargo test failed" }
cargo build --release
if ($LASTEXITCODE -ne 0) { throw "release build failed" }
cargo run --release -- capabilities
if ($LASTEXITCODE -ne 0) { throw "capabilities failed" }
cargo run --release -- check examples/rust_surface_0512.qr
if ($LASTEXITCODE -ne 0) { throw "modern syntax check failed" }
cargo run --release -- build examples/rust_surface_0512.qr --skip-unchanged
if ($LASTEXITCODE -ne 0) { throw "QASM build failed" }
& target/release/qrust.exe build-qcu examples/rust_surface_0512.qr
if ($LASTEXITCODE -ne 0) { throw "QCU interchange build failed" }
Write-Output "QRust 0.5.12 surface smoke checks completed."
