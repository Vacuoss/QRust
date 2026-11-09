param([switch]$SkipTests)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

# First validate the existing 0.5.23 suite and nine historical QASM/QCU
# programs against the pristine 0.5.21 control source
$ExistingSmoke = Join-Path $Root 'scripts/smoke_references_0523.ps1'
if ($SkipTests) { & $ExistingSmoke -SkipTests } else { & $ExistingSmoke }
if ($LASTEXITCODE -ne 0) { throw 'Existing reference compatibility suite failed' }

$Binary = Join-Path $Root 'target/release/qrust.exe'
if (-not (Test-Path -LiteralPath $Binary)) { $Binary = Join-Path $Root 'target/release/qrust' }
if (-not (Test-Path -LiteralPath $Binary)) { throw 'Missing compiled QRust release executable' }

$Temp = Join-Path $env:TEMP ('qrust-ref-ext-0523-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp -Force | Out-Null
try {
    foreach ($Pair in @(
        @{ Input = 'reference_extension_0523.qr'; Name = 'references' },
        @{ Input = 'reference_extension_0523_flat.qr'; Name = 'flat' }
    )) {
        $Source = Join-Path $Root ('benchmark_fixtures/' + $Pair.Input)
        $Output = Join-Path $Temp ($Pair.Name + '.qr')
        Copy-Item -LiteralPath $Source -Destination $Output
        & $Binary check $Output | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "Check failed: $($Pair.Name)" }
        & $Binary build $Output | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "QASM build failed: $($Pair.Name)" }
        & $Binary build-qcu $Output | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "QCU build failed: $($Pair.Name)" }
    }
    foreach ($Extension in @('qasm','qcu')) {
        $Refs = (Get-FileHash (Join-Path $Temp "references.${Extension}") -Algorithm SHA256).Hash
        $Flat = (Get-FileHash (Join-Path $Temp "flat.${Extension}") -Algorithm SHA256).Hash
        if ($Refs -ne $Flat) { throw "Reference extension changed ${Extension} output" }
        Write-Host "MATCH extension ${Extension} ${Refs}"
    }
    Write-Host 'PASS: nested immutable references, temporary reborrows and 0.5.21 compatibility'
}
finally { Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue }
