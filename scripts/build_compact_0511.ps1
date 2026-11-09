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
    if (-not (Test-Path -LiteralPath $Exe)) { throw "Executable missing: $Exe (this packaging script requires Windows)" }
    $Architecture = $env:PROCESSOR_ARCHITECTURE
    if (-not $Architecture) { $Architecture = 'unknown' }
    $Version = '0.5.11'
    $FolderName = "qrust-$Version-windows-$($Architecture.ToLowerInvariant())"
    $Dist = Join-Path $Root 'dist'
    $Stage = Join-Path $Dist $FolderName
    New-Item -ItemType Directory -Path $Dist -Force | Out-Null
    if (Test-Path -LiteralPath $Stage) { Remove-Item -LiteralPath $Stage -Force -Recurse }
    New-Item -ItemType Directory -Path $Stage -Force | Out-Null
    Copy-Item -LiteralPath $Exe -Destination (Join-Path $Stage 'qrust.exe')
    Copy-Item -LiteralPath (Join-Path $Root 'LICENSE') -Destination (Join-Path $Stage 'LICENSE')
    @'
QRust 0.5.11 - portable Windows executable

No installer or separate DLL bundle is included. The executable is compiled
from Rust's standard library without third-party Rust dependencies.

Usage from PowerShell:
  .\qrust.exe help
  .\qrust.exe check my_circuit.qr
  .\qrust.exe build my_circuit.qr --skip-unchanged
  .\qrust.exe build-qcu my_circuit.qr
  .\qrust.exe inspect-qcu my_circuit.qcu

Normal builds safely replace .qasm outputs with streamed data. To check the
compiler's source-level test suite, run `cargo test` in the source package.

Packed EXE size and compatibility depend on your Rust toolchain and target.
'@ | Set-Content -LiteralPath (Join-Path $Stage 'README.txt') -Encoding UTF8
    if ($UseUpx) {
        $Upx = Get-Command upx -ErrorAction SilentlyContinue
        if (-not $Upx) { throw 'UPX not found. Install it or omit -UseUpx.' }
        Write-Warning 'UPX can cause antivirus false positives. This is opt-in.'
        & $Upx.Source --best --lzma (Join-Path $Stage 'qrust.exe')
        if ($LASTEXITCODE -ne 0) { throw 'UPX compression failed' }
    }
    $Zip = Join-Path $Dist ("$FolderName.zip")
    if (Test-Path -LiteralPath $Zip) { Remove-Item -LiteralPath $Zip -Force }
    Compress-Archive -Path $Stage -DestinationPath $Zip -CompressionLevel Optimal
    Write-Host "Portable ZIP: $Zip"
    $ExeBytes = (Get-Item -LiteralPath (Join-Path $Stage 'qrust.exe')).Length
    $ZipBytes = (Get-Item -LiteralPath $Zip).Length
    Write-Host ("EXE: {0:N0} bytes; ZIP: {1:N0} bytes" -f $ExeBytes, $ZipBytes)
    if ($Use7Zip) {
        $Seven = Get-Command 7z -ErrorAction SilentlyContinue
        if (-not $Seven) { $Seven = Get-Command 7za -ErrorAction SilentlyContinue }
        if (-not $Seven) { throw '7-Zip command not found. ZIP was still generated.' }
        $Archive = Join-Path $Dist ("$FolderName.7z")
        if (Test-Path -LiteralPath $Archive) { Remove-Item -LiteralPath $Archive -Force }
        & $Seven.Source a -t7z -mx=9 -m0=lzma2 -ms=on $Archive $Stage
        if ($LASTEXITCODE -ne 0) { throw '7-Zip packaging failed' }
        Write-Host "Maximum-compression archive: $Archive"
    }
    if ($CleanCache) {
        Write-Warning 'Removing Cargo build caches (target/). Next build will recompile.'
        cargo clean
        if ($LASTEXITCODE -ne 0) { throw 'cargo clean failed' }
    }
}
finally { Pop-Location }
