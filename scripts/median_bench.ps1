param(
    [int]$Runs = 5,
    [int]$CoreIterations = 100000,
    [int]$StressIterations = 200
)

$ErrorActionPreference = "Stop"
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
Push-Location $projectRoot
try {
    & cargo build --release
    if ($LASTEXITCODE -ne 0) { throw "Release build failed: refusing to benchmark an old executable" }
} finally {
    Pop-Location
}
$exe = Join-Path $projectRoot "target\release\qrust.exe"
if (-not (Test-Path $exe)) { throw "Release executable missing after successful build" }

function Measure-QRust {
    param([string]$Source, [int]$Iterations)
    $measurements = @()
    for ($i = 0; $i -lt $Runs; $i++) {
        $output = (& $exe bench $Source $Iterations 2>&1 | Out-String)
        if ($LASTEXITCODE -ne 0) { throw "Benchmark failed: $output" }
        if ($output -notmatch '(?m)^\d+ parses \+ semantic checks in ([0-9.]+) ms') {
            throw "Could not parse benchmark output: $output"
        }
        $measurements += [double]::Parse($Matches[1], [Globalization.CultureInfo]::InvariantCulture)
    }
    $sorted = @($measurements | Sort-Object)
    $mid = [int][math]::Floor($sorted.Count / 2)
    if ($sorted.Count % 2 -eq 0) {
        $median = ($sorted[$mid - 1] + $sorted[$mid]) / 2
    } else { $median = $sorted[$mid] }
    [pscustomobject]@{
        Source = $Source
        Iterations = $Iterations
        Runs = $Runs
        MedianMs = [math]::Round($median, 3)
        MicrosecondsPerCompile = [math]::Round(($median * 1000) / $Iterations, 3)
    }
}

Measure-QRust "examples/core_gates.qr" $CoreIterations
Measure-QRust "examples/function_stress.qr" $StressIterations
