param(
    [int]$MemoryBudgetMiB = 1024,
    [int]$Repeats = 3,
    [switch]$IncludeStringStress
)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    & (Join-Path $PSScriptRoot 'restore_benchmark_examples.ps1') -RepairMissing
    # PowerShell script reports errors with throw; LASTEXITCODE is not updated by PowerShell cmdlets
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path -LiteralPath $Exe)) { throw "Executable not found: $Exe" }
    $Directory = Join-Path $Root 'benchmark_results'
    New-Item -ItemType Directory -Force -Path $Directory | Out-Null
    $Stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
    $Log = Join-Path $Directory "qrust-0.5.14-expr.1-$Stamp.txt"
    $Results = New-Object System.Collections.Generic.List[object]
    function Invoke-Metric([string]$Label, [string[]]$Command, [int]$Iteration) {
        $Watch = [System.Diagnostics.Stopwatch]::StartNew()
        $Out = & $Exe @Command 2>&1
        $Exit = $LASTEXITCODE
        $Watch.Stop()
        $Header = "==== $Label run $Iteration : $($Watch.Elapsed.TotalMilliseconds.ToString('F3')) ms ===="
        $Header | Out-File -FilePath $Log -Encoding utf8 -Append
        $Out | Out-File -FilePath $Log -Encoding utf8 -Append
        if ($Exit -ne 0) { throw "$Label failed with exit $Exit; see $Log" }
        $script:Results.Add([pscustomobject]@{
            Test = $Label; Run = $Iteration; WallMs = [math]::Round($Watch.Elapsed.TotalMilliseconds,3)
        })
    }
    foreach ($Source in @('core_gates.qr', 'loop_indexed_053.qr', 'function_stress.qr')) {
        for ($r=1; $r -le $Repeats; $r++) { Invoke-Metric "parse-$Source" @('bench',"examples/$Source",'500','--detailed') $r }
    }
    foreach ($Size in @(10000,100000,500000)) {
        for ($r=1; $r -le $Repeats; $r++) {
            Invoke-Metric "stream-$Size" @('bench-stress-stream',"$Size", "$MemoryBudgetMiB") $r
            if ($IncludeStringStress) {
                Invoke-Metric "string-$Size" @('bench-stress',"$Size", "$MemoryBudgetMiB") $r
            }
        }
    }
    $Csv = Join-Path $Directory "qrust-0.5.14-expr.1-$Stamp.csv"
    $Results | Export-Csv -LiteralPath $Csv -NoTypeInformation -Encoding utf8
    $Results | Group-Object Test | ForEach-Object {
        $m = @($_.Group | Sort-Object WallMs)
        $n = $m.Count
        $median = if ($n % 2) { $m[[int][math]::Floor($n/2)].WallMs } else { ($m[$n/2-1].WallMs+$m[$n/2].WallMs)/2 }
        [pscustomobject]@{ Test=$_.Name; Samples=$n; MedianWallMs=[math]::Round($median,3); MinWallMs=$m[0].WallMs; MaxWallMs=$m[$n-1].WallMs }
    } | Format-Table -AutoSize
    Write-Host "Raw results: $Log"
    Write-Host "CSV: $Csv"
} finally { Pop-Location }
