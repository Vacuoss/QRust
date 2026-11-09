param([switch]$RepairMissing)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$FixtureDir = Join-Path $Root 'benchmark_fixtures'
$ExamplesDir = Join-Path $Root 'examples'
if (-not (Test-Path -LiteralPath $ExamplesDir -PathType Container)) { New-Item -ItemType Directory -Force -Path $ExamplesDir | Out-Null }
$Required = @{
    "core_gates.qr" = "FA0C21A8154D1600170BAC1D4C286F43BF89320F388DAD1737676BBA606F5FD4"
    "loop_indexed_053.qr" = "CB79A04F9FF230FAC21507EF6024F8FC046465F498B863BFC9C524741DF9CEFE"
    "function_stress.qr" = "554ACAF69A8469E0EEA4085AB04E8D7224219F84E8070B6D8D36ABCCEDEC2EB8"
    "loop_parametric_054.qr" = "D07819C46327CDE8D79AFA1DFC9CD72C7CF2335DFBD7A6674E451B2889A64086"
}
foreach ($Name in ($Required.Keys | Sort-Object)) {
    $Master = Join-Path $FixtureDir $Name
    $Target = Join-Path $ExamplesDir $Name
    if (-not (Test-Path -LiteralPath $Master -PathType Leaf)) { throw "Missing shipped benchmark fixture: $Master" }
    $MasterHash = (Get-FileHash -LiteralPath $Master -Algorithm SHA256).Hash
    if ($MasterHash -ne $Required[$Name]) { throw "Corrupt shipped benchmark fixture: $Master" }
    if (-not (Test-Path -LiteralPath $Target -PathType Leaf)) {
        if (-not $RepairMissing) { throw "Missing benchmark example: $Target; run scripts/restore_benchmark_examples.ps1 -RepairMissing" }
        Copy-Item -LiteralPath $Master -Destination $Target
        Write-Host "Restored: $Target"
    } else {
        $CurrentHash = (Get-FileHash -LiteralPath $Target -Algorithm SHA256).Hash
        if ($CurrentHash -ne $Required[$Name]) {
            throw "Modified benchmark example: $Target. Refusing to overwrite user changes. Restore from benchmark_fixtures manually for a comparable run."
        }
    }
}
Write-Host "Benchmark examples verified: $($Required.Count)"
