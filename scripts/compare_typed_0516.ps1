$ErrorActionPreference = 'Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Fixture=Join-Path $Root 'reference/QRust_0.5.15_clean_source.zip'
if (-not (Test-Path $Fixture)) {throw '0.5.15 control archive missing'}
$Tmp=Join-Path $env:TEMP ('qrust-typed-diff-'+[guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Tmp | Out-Null
try {
    $Old=Join-Path $Tmp 'old'
    Expand-Archive -LiteralPath $Fixture -DestinationPath $Old
    Push-Location $Old
    try {cargo build --release;if($LASTEXITCODE -ne 0){throw 'baseline build failed'}}finally{Pop-Location}
    Push-Location $Root
    try {cargo build --release;if($LASTEXITCODE -ne 0){throw 'new build failed'}}finally{Pop-Location}
    $OldExe=Join-Path $Old 'target/release/qrust.exe'
    $NewExe=Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $OldExe)) {$OldExe=Join-Path $Old 'target/release/qrust'}
    if (-not (Test-Path $NewExe)) {$NewExe=Join-Path $Root 'target/release/qrust'}
    foreach ($Name in @('bell','core_gates','function_stress','loop_indexed_053','static_loop_control_0513','rust_static_0515','rust_exact_large_0515')) {
        foreach ($V in @('old','new')) {
            $Dir=Join-Path $Tmp "$V-out";New-Item -ItemType Directory -Path $Dir -Force|Out-Null
            Copy-Item -LiteralPath (Join-Path $Root "examples/$Name.qr") -Destination (Join-Path $Dir "$Name.qr") -Force
            $Exe=if($V -eq 'old'){$OldExe}else{$NewExe}
            & $Exe build (Join-Path $Dir "$Name.qr") | Out-Null
            if($LASTEXITCODE -ne 0){throw "$Name $V QASM failed"}
            & $Exe build-qcu (Join-Path $Dir "$Name.qr") | Out-Null
            if($LASTEXITCODE -ne 0){throw "$Name $V QCU failed"}
        }
        foreach ($Ext in @('qasm','qcu')) {
            $A=(Get-FileHash (Join-Path $Tmp "old-out/$Name.$Ext") -Algorithm SHA256).Hash
            $B=(Get-FileHash (Join-Path $Tmp "new-out/$Name.$Ext") -Algorithm SHA256).Hash
            if($A -ne $B){throw "MISMATCH $Name.$Ext"}
            Write-Host "MATCH $Name.$Ext : $B"
        }
    }
    Write-Host 'PASS: 7 previous programs, QASM/QCU byte-identical'
} finally {Remove-Item -LiteralPath $Tmp -Recurse -Force -ErrorAction SilentlyContinue}
exit 0
