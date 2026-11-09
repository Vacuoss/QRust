$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Fixture=Join-Path $Root 'reference/QRust_0.5.17_profiled_control.zip'
if(-not(Test-Path $Fixture)){throw '0.5.17 control archive missing; use full ZIP'}
$Temp=Join-Path $env:TEMP ('qrust-compat-0518-'+[guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp -Force|Out-Null
try {
    $Old=Join-Path $Temp 'old';Expand-Archive -LiteralPath $Fixture -DestinationPath $Old
    foreach($Dir in @($Old,$Root)){
        Push-Location $Dir
        try{cargo build --release;if($LASTEXITCODE -ne 0){throw "build failed: $Dir"}}
        finally{Pop-Location}
    }
    $OldExe=Join-Path $Old 'target/release/qrust.exe';$NewExe=Join-Path $Root 'target/release/qrust.exe'
    if(-not(Test-Path $OldExe)){$OldExe=Join-Path $Old 'target/release/qrust'}
    if(-not(Test-Path $NewExe)){$NewExe=Join-Path $Root 'target/release/qrust'}
    $Files=@('bell','core_gates','function_stress','loop_indexed_053','static_loop_control_0513',
        'rust_static_0515','rust_exact_large_0515','rust_typed_0516','rust_typed_ownership_0516')
    foreach($Name in $Files){
        $Choices=@([pscustomobject]@{Tag='old';Exe=$OldExe},[pscustomobject]@{Tag='new';Exe=$NewExe})
        foreach($Choice in $Choices){
            $Tag=$Choice.Tag;$Exe=$Choice.Exe;$Dst=Join-Path $Temp $Tag
            New-Item -ItemType Directory -Path $Dst -Force|Out-Null
            $File=Join-Path $Dst "$Name.qr"
            Copy-Item -LiteralPath (Join-Path $Root "examples/$Name.qr") -Destination $File -Force
            & $Exe build $File | Out-Null;if($LASTEXITCODE -ne 0){throw "$Tag $Name QASM failed"}
            & $Exe build-qcu $File | Out-Null;if($LASTEXITCODE -ne 0){throw "$Tag $Name QCU failed"}
        }
        foreach($Ext in @('qasm','qcu')){
            $A=(Get-FileHash (Join-Path $Temp "old/$Name.$Ext") -Algorithm SHA256).Hash
            $B=(Get-FileHash (Join-Path $Temp "new/$Name.$Ext") -Algorithm SHA256).Hash
            if($A -ne $B){throw "MISMATCH $Name.$Ext"}
            Write-Host "MATCH $Name.$Ext $A"
        }
    }
    Write-Host "PASS: $($Files.Count) shared programs, QASM and QCU byte-identical to 0.5.17"
}finally{Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue}
