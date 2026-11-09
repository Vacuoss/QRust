param([int]$Repeats = 5, [int]$Iterations = 20)
$ErrorActionPreference = 'Stop'
if ($Repeats -lt 1 -or $Iterations -lt 1) { throw 'Repeats and Iterations must be positive' }
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Archive = Join-Path $Root 'reference/QRust_0.5.14_expr_fixed_baseline.zip'
if (-not (Test-Path $Archive)) { throw 'Missing baseline archive (use full ZIP)' }
$Workspace = Join-Path ([IO.Path]::GetTempPath()) ("qrust-ast-bench-" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $Workspace | Out-Null
try {
    $Base = Join-Path $Workspace 'baseline'
    Expand-Archive -LiteralPath $Archive -DestinationPath $Base
    $OldRoot = Join-Path $Base 'QRust_Core_0.5.14_expr_preview'
    $OldExe = Join-Path $Workspace 'old-target/release/qrust.exe'
    $NewExe = Join-Path $Root 'target/release/qrust.exe'
    & cargo build --release --manifest-path (Join-Path $OldRoot 'Cargo.toml') --target-dir (Join-Path $Workspace 'old-target')
    if ($LASTEXITCODE -ne 0) { throw 'baseline build failed' }
    & cargo build --release --manifest-path (Join-Path $Root 'Cargo.toml')
    if ($LASTEXITCODE -ne 0) { throw 'candidate build failed' }
    $Results = New-Object System.Collections.Generic.List[object]
    foreach ($Example in @('arena_long_0514.qr', 'core_gates.qr', 'loop_indexed_053.qr')) {
        $Src = Join-Path $Root "examples/$Example"
        if (-not (Test-Path $Src)) { throw "missing benchmark example: $Src" }
        foreach ($Variant in @(@{Name='0.5.14-expr.1';Exe=$OldExe},@{Name='0.5.14-ast.2';Exe=$NewExe})) {
            for ($Rep=1; $Rep -le $Repeats; $Rep++) {
                $Output = & $Variant.Exe bench-stages $Src $Iterations
                if ($LASTEXITCODE -ne 0) { throw "benchmark failed ($Example / $($Variant.Name))" }
                foreach ($Line in $Output) {
                    if ($Line -match '^\s*(Lexer|Parser|Lowering|Semantic Check)\s+median\s+([0-9.]+)\s+us\s+mean\s+([0-9.]+)\s+us') {
                        $Results.Add([pscustomobject]@{
                            Version=$Variant.Name;Example=$Example;Run=$Rep;Stage=$Matches[1];
                            MedianUs=[double]::Parse($Matches[2], [Globalization.CultureInfo]::InvariantCulture);
                            MeanUs=[double]::Parse($Matches[3], [Globalization.CultureInfo]::InvariantCulture)
                        })
                    }
                }
            }
        }
    }
    if ($Results.Count -ne (3 * 2 * $Repeats * 4)) { throw "expected stage rows missing: $($Results.Count)" }
    $OutputDir = Join-Path $Root 'benchmark_results'
    New-Item -ItemType Directory -Force $OutputDir | Out-Null
    $Csv = Join-Path $OutputDir ("ast2-comparison-" + (Get-Date -Format yyyyMMdd-HHmmss) + '.csv')
    $Results | Export-Csv -Path $Csv -NoTypeInformation -Encoding utf8
    Write-Host "Saved per-stage baseline comparison: $Csv"
} finally { Remove-Item -LiteralPath $Workspace -Force -Recurse -ErrorAction SilentlyContinue }
