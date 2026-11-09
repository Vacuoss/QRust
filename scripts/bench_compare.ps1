param(
    [string]$InputFile = "examples/core_gates.qr",
    [int]$Iterations = 100000,
    [int]$Runs = 5
)
$ErrorActionPreference = "Stop"
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
if (-not (Test-Path $exe)) {
    throw "Release executable not found. Run: cargo build --release"
}
if (-not (Test-Path $InputFile)) { throw "Input not found: $InputFile" }
if ($Iterations -lt 1 -or $Iterations -gt 1000000 -or $Runs -lt 1) {
    throw "Use 1..1000000 iterations and at least one run"
}
& $exe bench $InputFile 1000 | Out-Null
$results = @()
for ($i = 1; $i -le $Runs; $i++) {
    $output = (& $exe bench $InputFile $Iterations) -join "`n"
    if ($LASTEXITCODE -ne 0) { throw "Benchmark failed: $output" }
    $match = [regex]::Match($output, 'in\s+([0-9]+(?:\.[0-9]+)?)\s+ms')
    if (-not $match.Success) { throw "Could not parse time: $output" }
    $milliseconds = [double]::Parse($match.Groups[1].Value, [System.Globalization.CultureInfo]::InvariantCulture)
    $results += $milliseconds
    Write-Host ("Run {0}/{1}: {2:N3} ms" -f $i, $Runs, $milliseconds)
}
$sorted = @($results | Sort-Object)
if ($Runs % 2 -eq 1) {
    $median = $sorted[[int][Math]::Floor($Runs / 2)]
} else {
    $median = ($sorted[$Runs / 2 - 1] + $sorted[$Runs / 2]) / 2
}
Write-Host ("Median: {0:N3} ms, {1:N3} us/compile" -f $median, ($median * 1000 / $Iterations))
Write-Host 'Detailed stage breakdown (not comparable to ordinary timing):'
& $exe bench $InputFile 1000 --detailed
