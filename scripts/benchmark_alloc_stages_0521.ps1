param([int]$Iterations=1000)
$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$ControlZip=Join-Path $Root 'reference/QRust_0.5.20_profile_instrumented_control.zip'
if(-not(Test-Path $ControlZip)){throw 'Instrumented 0.5.20 control archive missing'}
$Temp=Join-Path $env:TEMP ('qrust-alloc-0521-'+[guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp -Force | Out-Null
if($Iterations -lt 1){throw 'Iterations must be positive'}
try {
    $Control=Join-Path $Temp 'old'
    Expand-Archive -LiteralPath $ControlZip -DestinationPath $Control
    $Results=Join-Path $Root 'benchmark_results';New-Item -ItemType Directory -Path $Results -Force|Out-Null
    $Stamp=Get-Date -Format 'yyyyMMdd-HHmmss'
    $Csv=Join-Path $Results "alloc-stages-0521-$Stamp.csv"
    $Log=Join-Path $Results "alloc-stages-0521-$Stamp.txt"
    $Rows=@()
    $Builds=@([pscustomobject]@{label='0.5.20';dir=$Control},[pscustomobject]@{label='0.5.21';dir=$Root})
    foreach($Build in $Builds){
        Push-Location $Build.dir
        try {
            cargo build --release --features alloc-profile
            if($LASTEXITCODE -ne 0){throw "allocation-profiler build failed $($Build.label)"}
        } finally {Pop-Location}
        $Exe=Join-Path $Build.dir 'target/release/qrust.exe'
        if(-not(Test-Path $Exe)){$Exe=Join-Path $Build.dir 'target/release/qrust'}
        foreach($Fixture in @('core_gates','function_stress','rust_static_0515','rust_typed_0516','rust_typed_ownership_0516','rust_exact_large_0515')){
            $File=Join-Path $Root "examples/$Fixture.qr"
            $Output=(& $Exe bench-stages $File $Iterations | Out-String)
            if($LASTEXITCODE -ne 0){throw "benchmark failed: $($Build.label) $Fixture`n$Output"}
            "### $($Build.label) : $Fixture`n$Output" | Out-File -LiteralPath $Log -Append -Encoding UTF8
            Write-Host "[$($Build.label)/$Fixture]";Write-Host $Output
            foreach($Line in ($Output -split "`r?`n")){
                if($Line -match '^  stage allocations (Lexer|Parser|Lowering|Semantic Check): ([0-9.]+) calls/compile, ([0-9.]+) requested bytes/compile'){
                    $Rows += [pscustomobject]@{version=$Build.label;fixture=$Fixture;stage=$Matches[1];iterations=$Iterations;calls_per_compile=$Matches[2];bytes_per_compile=$Matches[3]}
                }
            }
        }
    }
    if($Rows.Count -ne 48){throw "expected 48 rows (2 versions x 6 fixtures x 4 stages), got $($Rows.Count)"}
    $Rows | Export-Csv -LiteralPath $Csv -NoTypeInformation -Encoding UTF8
    Write-Host "CSV: $Csv`nLog: $Log"
    Write-Host 'Both versions use identical profiling instrumentation. Bytes include successful reallocations; not OS RSS.'
} finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
