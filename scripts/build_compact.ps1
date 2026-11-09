param(
    [switch]$UseUpx,
    [switch]$Use7Zip,
    [switch]$RunTests,
    [switch]$CleanCache
)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    if ($RunTests) {
        cargo test
        if ($LASTEXITCODE -ne 0) { throw 'Tests failed; no portable package created' }
    }
    cargo build --profile compact
    if ($LASTEXITCODE -ne 0) { throw 'Compact build failed' }
    $Exe = Join-Path $Root 'target\compact\qrust.exe'
    if (-not (Test-Path -LiteralPath $Exe)) { throw 'This portable packaging script requires a Windows .exe build' }
    $Manifest = Get-Content -LiteralPath (Join-Path $Root 'Cargo.toml') -Raw
    $Match = [regex]::Match($Manifest, '(?m)^version\s*=\s*"([^"]+)"')
    if (-not $Match.Success) { throw 'Could not read package version from Cargo.toml' }
    $Version = $Match.Groups[1].Value
    $Architecture = $env:PROCESSOR_ARCHITECTURE
    if (-not $Architecture) { $Architecture = 'unknown' }
    $FolderName = "qrust-$Version-windows-$($Architecture.ToLowerInvariant())"
    $Dist = Join-Path $Root 'dist'
    $Stage = Join-Path $Dist $FolderName
    New-Item -ItemType Directory -Path $Dist -Force | Out-Null
    if (Test-Path -LiteralPath $Stage) { Remove-Item -LiteralPath $Stage -Force -Recurse }
    New-Item -ItemType Directory -Path $Stage -Force | Out-Null
    Copy-Item -LiteralPath $Exe -Destination (Join-Path $Stage 'qrust.exe')
    Copy-Item -LiteralPath (Join-Path $Root 'LICENSE') -Destination (Join-Path $Stage 'LICENSE')
    @"
QRust $Version - portable Windows executable

Run: qrust.exe help
     qrust.exe capabilities
     qrust.exe check your_program.qr
     qrust.exe build your_program.qr
     qrust.exe build-qcu your_program.qr

Rust-inspired quantum DSL, NOT a replacement for rustc.
"@ | Set-Content -LiteralPath (Join-Path $Stage 'README.txt') -Encoding UTF8
    if ($UseUpx) {
        $Upx = Get-Command upx -ErrorAction SilentlyContinue
        if (-not $Upx) { throw 'UPX missing; omit -UseUpx.' }
        Write-Warning 'UPX is optional and can trigger antivirus false positives.'
        & $Upx.Source --best --lzma (Join-Path $Stage 'qrust.exe')
        if ($LASTEXITCODE -ne 0) { throw 'UPX failed' }
    }
    $Zip = Join-Path $Dist "$FolderName.zip"
    if (Test-Path -LiteralPath $Zip) { Remove-Item -LiteralPath $Zip -Force }
    Compress-Archive -Path $Stage -DestinationPath $Zip -CompressionLevel Optimal
    Write-Host "Portable ZIP: $Zip"
    Write-Host ("EXE: {0:N0} bytes; ZIP: {1:N0} bytes" -f
        (Get-Item -LiteralPath (Join-Path $Stage 'qrust.exe')).Length,
        (Get-Item -LiteralPath $Zip).Length)
    if ($Use7Zip) {
        $Seven = Get-Command 7z -ErrorAction SilentlyContinue
        if (-not $Seven) { $Seven = Get-Command 7za -ErrorAction SilentlyContinue }
        if (-not $Seven) { throw '7-Zip not found; ZIP was created.' }
        $Archive = Join-Path $Dist "$FolderName.7z"
        if (Test-Path -LiteralPath $Archive) { Remove-Item -LiteralPath $Archive -Force }
        & $Seven.Source a -t7z -mx=9 -m0=lzma2 -ms=on $Archive $Stage
        if ($LASTEXITCODE -ne 0) { throw '7-Zip packaging failed' }
        Write-Host "7z archive: $Archive"
    }
    if ($CleanCache) {
        cargo clean
        if ($LASTEXITCODE -ne 0) { throw 'cargo clean failed' }
    }
} finally { Pop-Location }
