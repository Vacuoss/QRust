$ErrorActionPreference = "Stop"
cargo build --release
if ($LASTEXITCODE -ne 0) { throw "cargo build failed" }
foreach ($file in @("examples/core_gates.qr", "examples/function_stress.qr", "examples/loop_indexed_053.qr", "examples/loop_parametric_054.qr")) {
    Write-Host "Comparing String vs streamed OpenQASM: $file"
    cargo run --release -- bench-qasm $file 25
    if ($LASTEXITCODE -ne 0) { throw "QASM benchmark failed: $file" }
}
Write-Host "Peak RSS comparison (run each mode in a separate process)"
cargo run --release -- bench-stress 500000 1024
if ($LASTEXITCODE -ne 0) { throw "String stress failed" }
cargo run --release -- bench-stress-stream 500000 1024
if ($LASTEXITCODE -ne 0) { throw "Stream stress failed" }
