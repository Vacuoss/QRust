$ErrorActionPreference = 'Stop'
cargo test
if ($LASTEXITCODE -ne 0) { throw 'cargo test failed' }
cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$Exe = '.\target\release\qrust.exe'
$Source = 'examples\bell.qr'
$Output = 'examples\bell.qasm'
$OldBytes = if (Test-Path -LiteralPath $Output) { [IO.File]::ReadAllBytes((Resolve-Path $Output).Path) } else { $null }
try {
    & $Exe build $Source
    if ($LASTEXITCODE -ne 0) { throw 'default build failed' }
    $Expected = [IO.File]::ReadAllBytes((Resolve-Path $Output).Path)
    & $Exe build $Source --skip-unchanged
    if ($LASTEXITCODE -ne 0) { throw 'skip-unchanged build failed' }
    $After = [IO.File]::ReadAllBytes((Resolve-Path $Output).Path)
    if (-not ([Convert]::ToBase64String($Expected) -eq [Convert]::ToBase64String($After))) { throw 'skip modified bytes' }
    & $Exe build $Source --string
    if ($LASTEXITCODE -ne 0) { throw 'legacy String build failed' }
    $After = [IO.File]::ReadAllBytes((Resolve-Path $Output).Path)
    if (-not ([Convert]::ToBase64String($Expected) -eq [Convert]::ToBase64String($After))) { throw 'stream and String bytes differ' }
}
finally {
    if ($null -ne $OldBytes) { [IO.File]::WriteAllBytes((Join-Path (Get-Location) $Output), $OldBytes) }
    elseif (Test-Path -LiteralPath $Output) { Remove-Item -LiteralPath $Output -Force }
}
Write-Host 'QRust 0.5.10 smoke checks completed.'
