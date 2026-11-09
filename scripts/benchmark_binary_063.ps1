param(
    [int]$Rounds = 5,
    [int]$Iterations = 300,
    [int]$E2ERuns = 20,
    [string]$BaselineExe = '',
    [switch]$SkipBuild,
    [switch]$BuildCompact
)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
if ($Rounds -lt 3 -or $Iterations -lt 10 -or $E2ERuns -lt 3) {
    throw 'Use Rounds >= 3, Iterations >= 10 and E2ERuns >= 3.'
}
$Culture = [System.Globalization.CultureInfo]::InvariantCulture
function Median([double[]]$Data) {
    $a = @($Data | Sort-Object)
    if ($a.Count -eq 0) {throw 'Empty sample series'}
    $m = [int][Math]::Floor($a.Count / 2)
    if ($a.Count % 2 -eq 1) {return [double]$a[$m]}
    return ([double]$a[$m - 1] + [double]$a[$m]) / 2.0
}
function Execute([string]$Exe, [string[]]$ArgsList) {
    $text = (& $Exe @ArgsList 2>&1 | Out-String)
    if ($LASTEXITCODE -ne 0) {throw "QRust exited $LASTEXITCODE : $Exe`n$text"}
    return $text
}
Push-Location $Root
try {
    if (-not $SkipBuild) {
        cargo build --release
        if ($LASTEXITCODE -ne 0) {throw 'Release compilation failed'}
    }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path -LiteralPath $Exe)) {throw "Missing Windows executable: $Exe"}
    $Versions = @([pscustomobject]@{Label='Current';Exe=$Exe})
    if ($BaselineExe -ne '') {
        $OldPath = (Resolve-Path -LiteralPath $BaselineExe).Path
        $Versions += [pscustomobject]@{Label='Baseline';Exe=$OldPath}
    }
    $ResultsDir = Join-Path $Root 'benchmark_results'
    New-Item -ItemType Directory -Path $ResultsDir -Force | Out-Null
    $Stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
    $BinaryRows = @()
    foreach ($V in $Versions) {
        $Bytes = (Get-Item -LiteralPath $V.Exe).Length
        $BinaryRows += [pscustomobject]@{
            Version=$V.Label; Profile='release'; Executable=$V.Exe;
            BinaryBytes=$Bytes; BinaryMiB=[math]::Round($Bytes / 1MB, 3)
        }
    }
    if ($BuildCompact) {
        cargo build --profile compact
        if ($LASTEXITCODE -ne 0) {throw 'Compact build failed'}
        $Compact = Join-Path $Root 'target/compact/qrust.exe'
        $Bytes = (Get-Item -LiteralPath $Compact).Length
        $BinaryRows += [pscustomobject]@{
            Version='Current';Profile='compact';Executable=$Compact;
            BinaryBytes=$Bytes;BinaryMiB=[math]::Round($Bytes / 1MB, 3)
        }
    }
    $Fixtures = @(
        'benchmark_fixtures/core_gates.qr',
        'benchmark_fixtures/function_stress.qr',
        'benchmark_fixtures/loop_indexed_053.qr',
        'benchmark_fixtures/reference_cfg_branch_0523.qr',
        'benchmark_fixtures/reference_nll_0523.qr'
    )
    $StageRows = @()
    $E2ERows = @()
    foreach ($Fixture in $Fixtures) {
        $Path = Join-Path $Root $Fixture
        if (-not (Test-Path -LiteralPath $Path)) {throw "Fixture missing: $Path"}
        foreach ($V in $Versions) {
            [void](Execute $V.Exe -ArgsList @('bench-stages', $Path, '15'))
        }
        for ($Round=0; $Round -lt $Rounds; $Round++) {
            $Order = if ($Versions.Count -eq 2 -and $Round % 2 -eq 1) {
                @($Versions[1],$Versions[0])
            } else {$Versions}
            foreach ($V in $Order) {
                $StageOutput = Execute $V.Exe -ArgsList @('bench-stages', $Path, [string]$Iterations)
                $Found = 0
                foreach ($Line in ($StageOutput -split "`r?`n")) {
                    if ($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us\s+mean\s+([0-9.]+)\s+us') {
                        $StageRows += [pscustomobject]@{
                            Version=$V.Label;Fixture=$Fixture;Round=$Round;Stage=$Matches[1];
                            MedianUs=[double]::Parse($Matches[2],$Culture);
                            MeanUs=[double]::Parse($Matches[3],$Culture)
                        }
                        $Found++
                    }
                }
                if ($Found -ne 4) {throw "Could not extract four stages from $($V.Label) $Fixture`n$StageOutput"}
                $E2EOutput = Execute $V.Exe -ArgsList @('bench-e2e', $Path, [string]$E2ERuns)
                if ($E2EOutput -notmatch 'wall-clock:\s*([0-9.]+)\s+us/run') {
                    throw "Cannot parse end-to-end wall time: $E2EOutput"
                }
                $Wall = [double]::Parse($Matches[1],$Culture)
                $Peak = $null
                if ($E2EOutput -match 'Peak process RSS/working set:\s*([0-9.]+)\s+MiB') {
                    $Peak = [double]::Parse($Matches[1],$Culture)
                }
                $E2ERows += [pscustomobject]@{
                    Version=$V.Label;Fixture=$Fixture;Round=$Round;
                    WallUs=$Wall;PeakWorkingSetMiB=$Peak
                }
            }
        }
    }
    $BinaryCsv = Join-Path $ResultsDir "binary-size-063-$Stamp.csv"
    $StageCsv = Join-Path $ResultsDir "stages-063-$Stamp.csv"
    $E2ECsv = Join-Path $ResultsDir "end-to-end-063-$Stamp.csv"
    $SummaryPath = Join-Path $ResultsDir "summary-063-$Stamp.txt"
    $BinaryRows | Export-Csv -LiteralPath $BinaryCsv -NoTypeInformation -Encoding UTF8
    $StageRows | Export-Csv -LiteralPath $StageCsv -NoTypeInformation -Encoding UTF8
    $E2ERows | Export-Csv -LiteralPath $E2ECsv -NoTypeInformation -Encoding UTF8
    $Summary = New-Object System.Collections.Generic.List[string]
    $Summary.Add('QRust executable size: the final .exe bytes, excluding source and build intermediates')
    foreach ($B in $BinaryRows) {
        $Summary.Add(('{0} {1}: {2} bytes ({3} MiB) {4}' -f $B.Version,$B.Profile,$B.BinaryBytes,$B.BinaryMiB,$B.Executable))
    }
    foreach ($Fixture in $Fixtures) {
        foreach ($V in $Versions) {
            $samples = @($E2ERows | Where-Object { $_.Fixture -eq $Fixture -and $_.Version -eq $V.Label })
            $wall = Median ([double[]]@($samples | ForEach-Object {$_.WallUs}))
            $peaks = @($samples | Where-Object {$null -ne $_.PeakWorkingSetMiB})
            $peakMax = if ($peaks.Count) {($peaks | Measure-Object -Property PeakWorkingSetMiB -Maximum).Maximum} else {'n/a'}
            $Summary.Add(('{0} {1}: E2E median {2:N3} us/run; max peak working set {3} MiB' -f $V.Label,$Fixture,$wall,$peakMax))
            foreach ($Name in @('Lexer','Parser','Lowering','Semantic Check')) {
                $subset = @($StageRows | Where-Object { $_.Fixture -eq $Fixture -and $_.Version -eq $V.Label -and $_.Stage -eq $Name })
                $median = Median ([double[]]@($subset | ForEach-Object {$_.MedianUs}))
                $Summary.Add(('    {0}: median of stage medians {1:N3} us' -f $Name,$median))
            }
        }
    }
    $Summary.Add('Measurements are local to this host. E2E includes I/O and formatting, not execution on QPU.')
    $Summary | Set-Content -LiteralPath $SummaryPath -Encoding UTF8
    $Summary | ForEach-Object { Write-Host $_ }
    Write-Host "CSV files: $BinaryCsv ; $StageCsv ; $E2ECsv"
    Write-Host "Report: $SummaryPath"
} finally { Pop-Location }
