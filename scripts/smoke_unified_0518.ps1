$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try{
    cargo test; if($LASTEXITCODE -ne 0){throw 'unit tests failed'}
    cargo build --release; if($LASTEXITCODE -ne 0){throw 'release build failed'}
    $Exe=Join-Path $Root 'target/release/qrust.exe'
    if(-not (Test-Path $Exe)){$Exe=Join-Path $Root 'target/release/qrust'}
    foreach($Name in @('rust_unified_0518','rust_unified_top_level_0518','rust_static_0515','rust_exact_large_0515')){
        & $Exe build (Join-Path $Root "examples/$Name.qr") | Out-Null
        if($LASTEXITCODE -ne 0){throw "compile failed: $Name"}
        & $Exe build-qcu (Join-Path $Root "examples/$Name.qr") | Out-Null
        if($LASTEXITCODE -ne 0){throw "QCU failed: $Name"}
        Write-Host "PASS: $Name"
    }
    foreach($Name in @('rust_unified_overflow_0518','rust_unified_move_0518','rust_unified_alias_0518')){
        $previous=$ErrorActionPreference
        try {
            $ErrorActionPreference='Continue'
            & $Exe check (Join-Path $Root "examples/$Name.qr") *> $null
            $status=$LASTEXITCODE
        } finally { $ErrorActionPreference=$previous }
        if($status -eq 0){throw "expected failure did not occur: $Name"}
        Write-Host "PASS: $Name rejected"
    }
    powershell -ExecutionPolicy Bypass -File scripts/compare_unified_0518.ps1
    if($LASTEXITCODE -ne 0){throw 'QASM/QCU parity failed'}
    Write-Host 'PASS: QRust 0.5.18 unified typed pipeline smoke'
}finally{Pop-Location}
