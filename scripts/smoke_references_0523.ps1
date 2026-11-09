param([switch]$SkipTests)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Archive = Join-Path $Root 'reference/QRust_0.5.21_control_source.zip'
if (-not (Test-Path -LiteralPath $Archive)) { throw 'Missing clean 0.5.21 control archive' }
$Temp = Join-Path $env:TEMP ('qrust-refs-0523-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp -Force | Out-Null
try {
    $Old = Join-Path $Temp 'control'
    Expand-Archive -LiteralPath $Archive -DestinationPath $Old
    if (-not $SkipTests) {
        Push-Location $Root
        try { cargo test; if ($LASTEXITCODE -ne 0) { throw '0.5.23 unit tests failed' } }
        finally { Pop-Location }
    }
    foreach ($Dir in @($Old, $Root)) {
        Push-Location $Dir
        try { cargo build --release; if ($LASTEXITCODE -ne 0) { throw "Release build failed: ${Dir}" } }
        finally { Pop-Location }
    }
    $OldExe = Join-Path $Old 'target/release/qrust.exe'
    $NewExe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $OldExe)) { $OldExe = Join-Path $Old 'target/release/qrust' }
    if (-not (Test-Path $NewExe)) { $NewExe = Join-Path $Root 'target/release/qrust' }
    $Names = @('bell','core_gates','function_stress','loop_indexed_053','static_loop_control_0513',
        'rust_static_0515','rust_exact_large_0515','rust_typed_0516','rust_typed_ownership_0516')
    foreach ($Name in $Names) {
        foreach ($Side in @(@{Tag='old';Exe=$OldExe},@{Tag='new';Exe=$NewExe})) {
            $Dir = Join-Path $Temp $Side.Tag
            New-Item -ItemType Directory -Path $Dir -Force | Out-Null
            $File = Join-Path $Dir "${Name}.qr"
            Copy-Item -LiteralPath (Join-Path $Root "examples/${Name}.qr") -Destination $File -Force
            & $Side.Exe build $File | Out-Null
            if ($LASTEXITCODE -ne 0) { throw "QASM failed: $($Side.Tag) ${Name}" }
            & $Side.Exe build-qcu $File | Out-Null
            if ($LASTEXITCODE -ne 0) { throw "QCU failed: $($Side.Tag) ${Name}" }
        }
        foreach ($Ext in @('qasm','qcu')) {
            $A = (Get-FileHash (Join-Path $Temp "old/${Name}.${Ext}") -Algorithm SHA256).Hash
            $B = (Get-FileHash (Join-Path $Temp "new/${Name}.${Ext}") -Algorithm SHA256).Hash
            if ($A -ne $B) { throw "Mismatch: ${Name}.${Ext}" }
            Write-Host "MATCH ${Name}.${Ext} ${A}"
        }
    }
    $Fixture = Join-Path $Root 'benchmark_fixtures/reference_core_0523.qr'
    & $NewExe check $Fixture
    if ($LASTEXITCODE -ne 0) { throw 'New reference fixture failed' }
    & $NewExe build $Fixture | Out-Null
    if ($LASTEXITCODE -ne 0) { throw 'Reference fixture OpenQASM failed' }
    & $NewExe build-qcu $Fixture | Out-Null
    if ($LASTEXITCODE -ne 0) { throw 'Reference fixture QCU failed' }
    Write-Host 'PASS: 0.5.23 reference core and 0.5.21 byte compatibility'
}
finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
