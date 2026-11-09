param([int]$Iterations=1000,[int]$Rounds=5)
$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$ControlZip=Join-Path $Root 'reference/QRust_0.5.20_intern_control.zip'
if(-not(Test-Path $ControlZip)){throw '0.5.20 source control missing'}
if($Iterations -lt 10 -or $Rounds -lt 2){throw 'Use at least 10 iterations and 2 rounds'}
$Temp=Join-Path $env:TEMP ('qrust-alternating-0521-'+[guid]::NewGuid().ToString('N'))
$Results=Join-Path $Root 'benchmark_results'
New-Item -ItemType Directory -Path $Temp,$Results -Force | Out-Null
$Stamp=Get-Date -Format 'yyyyMMdd-HHmmss'
$Csv=Join-Path $Results "alternating-0521-$Stamp.csv"
$Summary=Join-Path $Results "alternating-0521-$Stamp.txt"
$Files=@('core_gates','function_stress','rust_static_0515','rust_typed_0516','rust_typed_ownership_0516','rust_exact_large_0515')
function Get-Median([double[]]$Values) {
    $Sorted=@($Values | Sort-Object)
    $N=$Sorted.Count
    if($N -eq 0){throw 'Cannot calculate median without samples'}
    if($N % 2 -eq 1){return [double]$Sorted[[int][math]::Floor($N/2)]}
    return ([double]$Sorted[($N/2)-1]+[double]$Sorted[$N/2])/2.0
}
try {
    $Old=Join-Path $Temp 'old';Expand-Archive -LiteralPath $ControlZip -DestinationPath $Old
    $Builds=@([pscustomobject]@{label='0.5.20';path=$Old},[pscustomobject]@{label='0.5.21';path=$Root})
    foreach($Build in $Builds){
        Push-Location $Build.path
        try {
            # Important: no --features alloc-profile here. Cargo selects a
            # different fingerprint and the ordinary System allocator
            cargo build --release
            if($LASTEXITCODE -ne 0){throw "build failed: $($Build.label)"}
        } finally {Pop-Location}
    }
    $Executables=@{}
    foreach($Build in $Builds){
        $Executable=Join-Path $Build.path 'target/release/qrust.exe'
        if(-not(Test-Path $Executable)){$Executable=Join-Path $Build.path 'target/release/qrust'}
        $Executables[$Build.label]=$Executable
    }
    $Rows=@()
    foreach($File in $Files){
        $Fixture=Join-Path $Root "examples/$File.qr"
        foreach($Build in $Builds){
            & $Executables[$Build.label] bench-stages $Fixture 50 | Out-Null
            if($LASTEXITCODE -ne 0){throw "warmup failed: $($Build.label) $File"}
        }
        for($Round=0;$Round -lt $Rounds;$Round++){
            # ABBA / BAAB ordering compensates for monotonic thermal drift
            $Order=if(($Round % 2) -eq 0){@('0.5.20','0.5.21','0.5.21','0.5.20')}
                else {@('0.5.21','0.5.20','0.5.20','0.5.21')}
            foreach($Version in $Order){
                $Output=(& $Executables[$Version] bench-stages $Fixture $Iterations | Out-String)
                if($LASTEXITCODE -ne 0){throw "failed $Version $File`n$Output"}
                $Metric=@{}
                foreach($Line in ($Output -split "`r?`n")){
                    if($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us'){
                        $Metric[$Matches[1]]=[double]::Parse($Matches[2],[cultureinfo]::InvariantCulture)
                    }
                }
                if($Metric.Count -ne 4){throw "Could not parse four stage medians: $Version $File"}
                $Rows += [pscustomobject]@{version=$Version;fixture=$File;round=$Round;iterations=$Iterations;
                    lexer_us=$Metric['Lexer'];parser_us=$Metric['Parser'];lowering_us=$Metric['Lowering'];sema_us=$Metric['Semantic Check'];
                    sum_stage_medians_us=$Metric['Lexer']+$Metric['Parser']+$Metric['Lowering']+$Metric['Semantic Check']}
            }
        }
        Write-Host "Completed: $File"
    }
    $Rows | Export-Csv -LiteralPath $Csv -NoTypeInformation -Encoding UTF8
    $Lines=@("QRust ordinary release (not alloc-profile) ABBA/BAAB benchmark", "Iterations per sample: $Iterations; rounds: $Rounds; samples per version/fixture: $(2*$Rounds)", '')
    foreach($File in $Files){
        $Lines+="[$File]"
        foreach($Metric in @('lexer_us','parser_us','lowering_us','sema_us','sum_stage_medians_us')){
            $OldVals=@($Rows|Where-Object {$_.fixture -eq $File -and $_.version -eq '0.5.20'}|ForEach-Object {[double]$_.$Metric})
            $NewVals=@($Rows|Where-Object {$_.fixture -eq $File -and $_.version -eq '0.5.21'}|ForEach-Object {[double]$_.$Metric})
            $Before=Get-Median $OldVals
            $After=Get-Median $NewVals
            $Percent=if($Before -ne 0){100*($After-$Before)/$Before}else{0}
            $Lines+=('{0,-24} 0.5.20 {1,10:F3} us  0.5.21 {2,10:F3} us  delta {3,7:F2}%' -f $Metric,$Before,$After,$Percent)
        }
        $Lines+=''
    }
    $Lines+='Note: sum_stage_medians_us is a diagnostic proxy, not end-to-end runtime. For total wall timing, use bench-e2e.'
    $Lines | Set-Content -LiteralPath $Summary -Encoding UTF8
    $Lines | ForEach-Object {Write-Host $_}
    Write-Host "CSV: $Csv`nSummary: $Summary"
} finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
