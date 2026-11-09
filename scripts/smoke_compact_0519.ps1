$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if($LASTEXITCODE -ne 0){throw 'unit tests failed'}
    cargo build --release
    if($LASTEXITCODE -ne 0){throw 'release build failed'}
    & (Join-Path $PSScriptRoot 'smoke_unified_memory_0518.ps1')
    & (Join-Path $PSScriptRoot 'compare_compact_0519.ps1')
    & ./target/release/qrust.exe check examples/compact_types_0519.qr
    if($LASTEXITCODE -ne 0){throw 'compact typed example failed'}
    Write-Host 'PASS: QRust compact aggregates and core memory candidate'
} finally {Pop-Location}
