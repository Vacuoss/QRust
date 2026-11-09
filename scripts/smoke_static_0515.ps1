$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'unit tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $Exe)) { $Exe = Join-Path $Root 'target/release/qrust' }
    foreach ($Example in @('rust_static_0515', 'rust_exact_large_0515')) {
        & $Exe check "examples/$Example.qr"
        if ($LASTEXITCODE -ne 0) { throw "$Example should compile" }
        & $Exe build-qcu "examples/$Example.qr"
        if ($LASTEXITCODE -ne 0) { throw "$Example QCU build failed" }
        Write-Host "PASS: $Example"
    }
    foreach ($Example in @('rust_overflow_0515', 'rust_precision_loss_0515')) {
        $Child = Start-Process -FilePath $Exe -ArgumentList @('check', "examples/$Example.qr") -Wait -PassThru -NoNewWindow
        if ($Child.ExitCode -eq 0) { throw "$Example was supposed to be rejected" }
        Write-Host "PASS: $Example rejected"
    }
    # Exact-type errors intentionally return 1; don't leave that as script status
    $global:LASTEXITCODE = 0
    Write-Host 'QRust static types preview smoke passed.'
} finally { Pop-Location }
