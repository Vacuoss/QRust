param(
    [Parameter(Mandatory = $true)][string]$BaselineExe,
    [string]$CandidateExe = '.\target\release\qrust.exe',
    [string]$InputFile = 'examples\core_gates.qr',
    [int]$Iterations = 100000,
    [int]$Runs = 5
)

$ErrorActionPreference = 'Stop'
if (-not (Test-Path $BaselineExe)) { throw "Baseline executable not found: $BaselineExe" }
if (-not (Test-Path $CandidateExe)) { throw "Candidate executable not found: $CandidateExe" }
if (-not (Test-Path $InputFile)) { throw "Input file not found: $InputFile" }
if ($Iterations -lt 1 -or $Iterations -gt 10000000 -or $Runs -lt 3) {
    throw 'Iterations must be in 1..10000000 and Runs must be >= 3'
}

function Invoke-QRustBench([string]$Executable, [int]$Count) {
    $output = (& $Executable bench $InputFile $Count) -join "`n"
    if ($LASTEXITCODE -ne 0) { throw "Benchmark failed ($Executable): $output" }
    $match = [regex]::Match($output, 'in\s+([0-9]+(?:\.[0-9]+)?)\s+ms')
    if (-not $match.Success) { throw "Unexpected benchmark output ($Executable): $output" }
    return [double]::Parse($match.Groups[1].Value,
        [System.Globalization.CultureInfo]::InvariantCulture)
}

function Get-Median([double[]]$Samples) {
    $ordered = @($Samples | Sort-Object)
    $mid = [int][Math]::Floor($ordered.Count / 2)
    if ($ordered.Count % 2 -eq 1) { return $ordered[$mid] }
    return ($ordered[$mid - 1] + $ordered[$mid]) / 2.0
}

# Warm both processes. Alternate order to reduce drift from frequency/temperature
[void](Invoke-QRustBench $BaselineExe 1000)
[void](Invoke-QRustBench $CandidateExe 1000)
$before = @()
$after = @()
for ($i = 0; $i -lt $Runs; $i++) {
    if ($i % 2 -eq 0) {
        $b = Invoke-QRustBench $BaselineExe $Iterations
        $c = Invoke-QRustBench $CandidateExe $Iterations
    } else {
        $c = Invoke-QRustBench $CandidateExe $Iterations
        $b = Invoke-QRustBench $BaselineExe $Iterations
    }
    $before += [double]$b
    $after += [double]$c
    Write-Host ('Run {0}: baseline={1:N3} ms, candidate={2:N3} ms' -f ($i + 1), $b, $c)
}
$baseline = Get-Median ([double[]]$before)
$candidate = Get-Median ([double[]]$after)
$delta = 100.0 * ($candidate / $baseline - 1.0)
Write-Host ('Median baseline: {0:N3} ms ({1:N3} us/compile)' -f $baseline, ($baseline * 1000.0 / $Iterations))
Write-Host ('Median candidate: {0:N3} ms ({1:N3} us/compile)' -f $candidate, ($candidate * 1000.0 / $Iterations))
Write-Host ('Relative elapsed time: {0:+0.00;-0.00;0.00}% (negative is faster)' -f $delta)
