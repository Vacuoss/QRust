param([int]$Iterations=500,[switch]$AllocationProfile)
$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Temp=Join-Path $env:TEMP ('qrust-perf-0518-'+[guid]::NewGuid().ToString('N'))
$BaselineZip=Join-Path $Root 'reference/QRust_0.5.17_profiled_control.zip'
if(-not(Test-Path $BaselineZip)){throw '0.5.17 control archive missing; use full ZIP'}
if($Iterations -le 0){throw 'Iterations must be positive'}
$Files=@('core_gates','rust_static_0515','rust_typed_0516','rust_typed_ownership_0516','rust_exact_large_0515')
$Results=Join-Path $Root 'benchmark_results'; New-Item -ItemType Directory -Path $Results -Force|Out-Null
$Stamp=Get-Date -Format yyyyMMdd-HHmmss
$Csv=Join-Path $Results "perf-0518-$Stamp.csv"
$Text=Join-Path $Results "perf-0518-$Stamp.txt"
New-Item -ItemType Directory -Path $Temp -Force|Out-Null
try {
    $Old=Join-Path $Temp 'old';Expand-Archive -LiteralPath $BaselineZip -DestinationPath $Old
    $Rows=@()
    $Builds=@([pscustomobject]@{Label='0.5.17';Directory=$Old},[pscustomobject]@{Label='0.5.18';Directory=$Root})
    foreach($Build in $Builds) {
        $Label=$Build.Label;$Directory=$Build.Directory
        Push-Location $Directory
        try {
            if($AllocationProfile){cargo build --release --features alloc-profile}
            else{cargo build --release}
            if($LASTEXITCODE -ne 0){throw "build failed: $Label"}
        } finally {Pop-Location}
        $Exe=Join-Path $Directory 'target/release/qrust.exe'
        if(-not(Test-Path $Exe)){$Exe=Join-Path $Directory 'target/release/qrust'}
        foreach($Name in $Files) {
            $Fixture=Join-Path $Root "examples/$Name.qr"
            $Output=(& $Exe bench-stages $Fixture $Iterations | Out-String)
            if($LASTEXITCODE -ne 0){throw "benchmark failed: $Label $Name`n$Output"}
            "### $Label : $Name`n$Output" | Out-File -LiteralPath $Text -Append -Encoding utf8
            Write-Host "[$Label/$Name]"; Write-Host $Output
            $Metrics=@{}
            foreach($Line in ($Output -split "`r?`n")) {
                if($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us') {
                    $Key=$Matches[1].Replace(' ','_');$Metrics[$Key]=$Matches[2]
                }
                if($Line -match 'live-payload peak/compile:\s+([0-9.]+) average bytes above baseline,\s+([0-9.]+) max bytes'){
                    $Metrics['peak_avg']=$Matches[1];$Metrics['peak_max']=$Matches[2]
                }
                if($Line -match 'allocations/compile:\s+([0-9.]+) calls,\s+([0-9.]+) requested bytes'){
                    $Metrics['calls']=$Matches[1];$Metrics['bytes']=$Matches[2]
                }
            }
            $Rows+=[pscustomobject]@{version=$Label;example=$Name;iterations=$Iterations
                lexer_us=$Metrics['Lexer'];parser_us=$Metrics['Parser'];lowering_us=$Metrics['Lowering'];sema_us=$Metrics['Semantic_Check']
                allocation_calls=$Metrics['calls'];requested_bytes=$Metrics['bytes'];
                peak_live_avg_bytes=$Metrics['peak_avg'];peak_live_max_bytes=$Metrics['peak_max']}
        }
    }
    $Rows | Export-Csv -LiteralPath $Csv -NoTypeInformation -Encoding UTF8
    Write-Host "CSV: $Csv";Write-Host "Log: $Text"
    Write-Host 'Note: same input files, same counter feature, same host; allocation bytes include reallocations.'
} finally {
    Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue
}
