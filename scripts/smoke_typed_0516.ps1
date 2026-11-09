$ErrorActionPreference = 'Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) {throw 'unit tests failed'}
    cargo build --release
    if ($LASTEXITCODE -ne 0) {throw 'release build failed'}
    $Exe=Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $Exe)) { $Exe=Join-Path $Root 'target/release/qrust' }
    foreach ($Name in @('rust_typed_0516','rust_typed_ownership_0516')) {
        & $Exe check "examples/$Name.qr"
        if ($LASTEXITCODE -ne 0) {throw "typed example $Name failed"}
        & $Exe build "examples/$Name.qr"
        if ($LASTEXITCODE -ne 0) {throw "QASM failed: $Name"}
        & $Exe build-qcu "examples/$Name.qr"
        if ($LASTEXITCODE -ne 0) {throw "QCU failed: $Name"}
        Write-Host "PASS: $Name"
    }
    foreach ($Name in @('rust_typed_move_error_0516','rust_typed_precision_error_0516')) {
        $OldPref=$ErrorActionPreference
        $ErrorActionPreference='Continue'
        try {
            $message=& $Exe check "examples/$Name.qr" 2>&1 | Out-String
            $ExitCode=$LASTEXITCODE
        } finally { $ErrorActionPreference=$OldPref }
        if ($ExitCode -eq 0) {throw "expected an error from $Name"}
        if ($Name -like '*move*' -and $message -notmatch 'moved value') {throw "missing move diagnostic: $message"}
        if ($Name -like '*precision*' -and $message -notmatch 'f64 QPU boundary') {throw "missing precision diagnostic: $message"}
        Write-Host "PASS: $Name correctly rejected"
    }
    Write-Host 'Typed host frontend smoke passed.'
} finally {Pop-Location}
exit 0
