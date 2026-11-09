$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try{
    cargo test; if($LASTEXITCODE -ne 0){throw 'unit tests failed'}
    cargo build --release; if($LASTEXITCODE -ne 0){throw 'release build failed'}
    powershell -ExecutionPolicy Bypass -File scripts/smoke_typed_0516.ps1
    if($LASTEXITCODE -ne 0){throw 'typed smoke failed'}
    powershell -ExecutionPolicy Bypass -File scripts/compare_perf_0517.ps1
    if($LASTEXITCODE -ne 0){throw 'QASM/QCU parity failed'}
    Write-Host 'PASS: QRust 0.5.17 performance candidate smoke'
}finally{Pop-Location}
