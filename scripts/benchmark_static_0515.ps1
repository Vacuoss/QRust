param([int]$Iterations = 500)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $Exe)) { $Exe = Join-Path $Root 'target/release/qrust' }
    & $Exe bench-stages examples/core_gates.qr $Iterations
    if ($LASTEXITCODE -ne 0) { throw 'legacy benchmark failed' }
    & $Exe bench-stages examples/rust_static_0515.qr $Iterations
    if ($LASTEXITCODE -ne 0) { throw 'typed Rust benchmark failed' }
} finally { Pop-Location }
