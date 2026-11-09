$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'unit regression tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    & (Join-Path $PSScriptRoot 'compare_names_0520.ps1')
    if ($LASTEXITCODE -ne 0) { throw 'byte-compatibility comparison failed' }
    & ./target/release/qrust.exe check examples/compact_types_0519.qr
    if ($LASTEXITCODE -ne 0) { throw 'typed frontend smoke failed' }
    Write-Host 'PASS: QRust 0.5.20 identifier interning candidate regressions'
} finally { Pop-Location }
