param([switch]$SkipTests)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

# Includes the 0.5.21 byte-identical baseline and Preview 3 tests
$Existing = Join-Path $Root 'scripts/smoke_reference_extension_0523.ps1'
if ($SkipTests) { & $Existing -SkipTests } else { & $Existing }
if ($LASTEXITCODE -ne 0) { throw 'Previous reference regressions failed' }

$Binary = Join-Path $Root 'target/release/qrust.exe'
if (-not (Test-Path -LiteralPath $Binary)) { $Binary = Join-Path $Root 'target/release/qrust' }
if (-not (Test-Path -LiteralPath $Binary)) { throw 'Missing release executable' }

$Temp = Join-Path $env:TEMP ('qrust-nll-0523-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp -Force | Out-Null
try {
    foreach ($InputName in @('reference_nll_0523','reference_nll_0523_flat','reference_lifetime_0523','reference_lifetime_0523_flat')) {
        $InputPath = Join-Path $Root ('benchmark_fixtures/' + $InputName + '.qr')
        $OutputPath = Join-Path $Temp ($InputName + '.qr')
        Copy-Item -LiteralPath $InputPath -Destination $OutputPath
        & $Binary check $OutputPath | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "Check failed: ${InputName}" }
        & $Binary build $OutputPath | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "QASM build failed: ${InputName}" }
        & $Binary build-qcu $OutputPath | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "QCU build failed: ${InputName}" }
    }
    foreach ($Ext in @('qasm','qcu')) {
        $Actual = (Get-FileHash -LiteralPath (Join-Path $Temp "reference_nll_0523.${Ext}") -Algorithm SHA256).Hash
        $Expected = (Get-FileHash -LiteralPath (Join-Path $Temp "reference_nll_0523_flat.${Ext}") -Algorithm SHA256).Hash
        if ($Actual -ne $Expected) { throw "NLL program changed ${Ext} output" }
        Write-Host "MATCH NLL ${Ext} ${Actual}"
    }
    # The reference-return smoke pair covers inferred `let s = forward(r)`;
    # previously that declaration was incorrectly sent to the quantum parser
    foreach ($Ext in @('qasm','qcu')) {
        $Actual = (Get-FileHash -LiteralPath (Join-Path $Temp "reference_lifetime_0523.${Ext}") -Algorithm SHA256).Hash
        $Expected = (Get-FileHash -LiteralPath (Join-Path $Temp "reference_lifetime_0523_flat.${Ext}") -Algorithm SHA256).Hash
        if ($Actual -ne $Expected) { throw "Reference lifetime return changed ${Ext} output" }
        Write-Host "MATCH lifetime ${Ext} ${Actual}"
    }
    Write-Host 'PASS: QRust 0.5.23 Preview 4 NLL, place and reborrow regression'
}
finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
