# QRust 0.6.15 static hybrid MIR regression and legacy fast-path checks
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    # Include compile-time fixtures; source-only bundles must be self-contained
    $missing = @()
    Get-ChildItem -Path (Join-Path $projectRoot 'src') -Filter '*.rs' -File -Recurse | ForEach-Object {
        $sourceFile = $_
        $text = Get-Content -LiteralPath $sourceFile.FullName -Raw
        foreach ($ref in [regex]::Matches($text, 'include_(?:str|bytes)!\s*\(\s*"([^"]+)"\s*\)')) {
            $path = Join-Path $sourceFile.DirectoryName $ref.Groups[1].Value
            if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { $missing += $path }
        }
    }
    if ($missing.Count) { throw "Missing fixtures: $($missing -join ', ')" }
    cargo test -- --quiet
    if ($LASTEXITCODE -ne 0) { throw '0.6.15 tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw '0.6.15 release build failed' }
    $exe = Join-Path $projectRoot 'target\release\qrust.exe'
    & $exe check-host (Join-Path $projectRoot 'examples\hybrid_coin_flip_0614.qr')
    if ($LASTEXITCODE -ne 0) { throw 'Hybrid MIR static check failed' }
    $out = & $exe run-host (Join-Path $projectRoot 'examples\hybrid_coin_flip_0614.qr') --seed 42 --input 100
    if ($LASTEXITCODE -ne 0) { throw 'Hybrid runtime smoke failed with nonzero status' }
    # Native executable output is a PowerShell string[] (one item per line)
    # `-notmatch` on an array returns nonmatching elements, which is truthy
    # even when one other line correctly reports "Total: 100"
    $outText = $out -join "`n"
    if ($outText -notmatch '(?m)^[ \t]*Total:[ \t]*100[ \t]*$') {
        throw "Hybrid runtime smoke failed: expected Total: 100. Output: $outText"
    }
    $out | Write-Output
    & $exe run (Join-Path $projectRoot 'examples\bell.qr') --shots 16 --seed 42
    if ($LASTEXITCODE -ne 0) { throw 'Legacy quantum fast-path failed' }
    Write-Output 'QRust 0.6.15 regressions complete.'
} finally { Pop-Location }
