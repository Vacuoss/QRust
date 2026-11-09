$ErrorActionPreference = 'Stop'
Push-Location (Join-Path $PSScriptRoot '..')
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'Cargo tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'Release build failed' }
    $exe = Join-Path (Get-Location) 'target/release/qrust.exe'
    if (-not (Test-Path $exe)) { $exe = Join-Path (Get-Location) 'target/release/qrust' }
    & $exe build-qcu examples/qcu_bell_0511.qr
    if ($LASTEXITCODE -ne 0) { throw 'QCU export failed' }
    & $exe inspect-qcu examples/qcu_bell_0511.qcu
    if ($LASTEXITCODE -ne 0) { throw 'QCU packet failed validation' }
    & $exe build-qcu examples/qcu_feedback_0511.qr
    if ($LASTEXITCODE -ne 0) { throw 'Feedback QCU export failed' }
    & $exe inspect-qcu examples/qcu_feedback_0511.qcu
    if ($LASTEXITCODE -ne 0) { throw 'Feedback QCU packet failed validation' }
    & $exe build examples/qcu_bell_0511.qr --skip-unchanged
    if ($LASTEXITCODE -ne 0) { throw 'QASM regression failed' }
    Write-Host 'QRust 0.5.11 QCU-neutral smoke checks completed.'
}
finally {
    Remove-Item 'examples/qcu_bell_0511.qcu', 'examples/qcu_feedback_0511.qcu', 'examples/qcu_bell_0511.qasm' -ErrorAction SilentlyContinue
    Pop-Location
}
