param([int]$Iterations = 500, [int]$Repeats = 3, [int]$LongIterations = 20)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    & (Join-Path $PSScriptRoot 'restore_benchmark_examples.ps1') -RepairMissing
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    $Results = New-Object System.Collections.Generic.List[object]
    foreach ($Source in @('core_gates.qr','function_stress.qr','loop_indexed_053.qr','loop_parametric_054.qr')) {
        for ($Rep=1; $Rep -le $Repeats; $Rep++) {
            $Text = & $Exe bench-stages "examples/$Source" $Iterations
            if ($LASTEXITCODE -ne 0) { throw "stage benchmark failed: $Source" }
            $Text
            foreach ($Line in $Text) {
                if ($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us\s+mean\s+([0-9.]+)\s+us') {
                    $Results.Add([pscustomobject]@{Example=$Source;Run=$Rep;Stage=$Matches[1];MedianUs=[double]::Parse($Matches[2],[cultureinfo]::InvariantCulture);MeanUs=[double]::Parse($Matches[3],[cultureinfo]::InvariantCulture)})
                }
            }
        }
    }
    # This is a new-language benchmark, not a byte parity test against the old parser
    for ($Rep=1; $Rep -le $Repeats; $Rep++) {
        $Text = & $Exe bench-stages 'examples/arena_long_0514.qr' $LongIterations
        if ($LASTEXITCODE -ne 0) { throw 'long-expression stage benchmark failed' }
        $Text
        foreach ($Line in $Text) {
            if ($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us\s+mean\s+([0-9.]+)\s+us') {
                $Results.Add([pscustomobject]@{Example='arena_long_0514.qr';Run=$Rep;Stage=$Matches[1];MedianUs=[double]::Parse($Matches[2],[cultureinfo]::InvariantCulture);MeanUs=[double]::Parse($Matches[3],[cultureinfo]::InvariantCulture)})
            }
        }
    }
    $Dir=Join-Path $Root 'benchmark_results'
    New-Item -ItemType Directory -Force -Path $Dir | Out-Null
    $Out=Join-Path $Dir "qrust-expr-stage-$(Get-Date -Format yyyyMMdd-HHmmss).csv"
    $Results | Export-Csv -LiteralPath $Out -NoTypeInformation -Encoding utf8
    if ($Results.Count -ne 5*4*$Repeats) { throw "incomplete stage data, collected $($Results.Count) rows" }
    Write-Host "Stage CSV: $Out"
} finally { Pop-Location }
