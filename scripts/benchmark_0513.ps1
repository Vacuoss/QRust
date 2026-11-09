$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    & $Exe bench examples/core_gates.qr 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw 'core benchmark failed' }
    & $Exe bench examples/loop_indexed_053.qr 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw 'indexed-loop benchmark failed' }
    & $Exe bench-stress-stream 500000 1024
    if ($LASTEXITCODE -ne 0) { throw 'streaming stress failed' }
    Write-Host 'QRust 0.5.13 benchmark checks completed; compare with the same 0.5.12 build.'
} finally { Pop-Location }
