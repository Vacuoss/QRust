$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if($LASTEXITCODE -ne 0){throw 'unit tests failed'}
    cargo build --release
    if($LASTEXITCODE -ne 0){throw 'release build failed'}
    powershell -ExecutionPolicy Bypass -File scripts/smoke_unified_0518.ps1
    if($LASTEXITCODE -ne 0){throw 'unified smoke failed'}
    & ./target/release/qrust.exe check examples/rust_unified_memory_0518.qr
    if($LASTEXITCODE -ne 0){throw 'typed memory example failed'}
    Write-Host 'PASS: unified memory hotfix smoke'
} finally {Pop-Location}
