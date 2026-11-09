$ErrorActionPreference = 'Stop'
# Detect incomplete distributions before invoking rustc
# `include_str!` / `include_bytes!` files are required at compile time even in tests
$sourceDir = Join-Path $PSScriptRoot '..\src'
$missing = @()
foreach ($sourceFile in (Get-ChildItem -LiteralPath $sourceDir -Filter '*.rs' -File -Recurse)) {
    $sourceText = Get-Content -LiteralPath $sourceFile.FullName -Raw
    $refs = [regex]::Matches($sourceText, 'include_(?:str|bytes)!\s*\(\s*"([^"]+)"\s*\)')
    foreach ($ref in $refs) {
        $refPath = Join-Path $sourceFile.DirectoryName $ref.Groups[1].Value
        if (-not (Test-Path -LiteralPath $refPath -PathType Leaf)) {
            $missing += "${sourceFile}: $($ref.Groups[1].Value)"
        }
    }
}
if ($missing.Count -gt 0) {
    throw ("Missing QRust compile-time assets:`n" + ($missing -join "`n") + "`nExtract the complete Fix 1 archive, including benchmark_fixtures/ and examples/.")
}

cargo test -- --quiet
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.14 tests failed' }
cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'QRust 0.6.14 release build failed' }
$exe = Join-Path $PSScriptRoot '..\target\release\qrust.exe'
$coin = Join-Path $PSScriptRoot '..\examples\hybrid_coin_flip_0614.qr'
$out = & $exe run $coin --seed 42 --input 100
if ($LASTEXITCODE -ne 0) { throw 'Hybrid coin smoke failed with nonzero status' }
$out | Write-Output
$outText = $out -join "`n"
if ($outText -notmatch '(?m)^[ \t]*Total:[ \t]*100[ \t]*$') {
    throw "Hybrid coin result did not sum to 100. Output: $outText"
}
$bell = Join-Path $PSScriptRoot '..\examples\bell.qr'
& $exe run $bell --shots 16 --seed 42
if ($LASTEXITCODE -ne 0) { throw 'Legacy quantum runner regression' }
Write-Output 'Hybrid and quantum smoke tests completed.'
