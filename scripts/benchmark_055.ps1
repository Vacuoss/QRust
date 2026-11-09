$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/core_gates.qr', 'examples/function_stress.qr',
                    'examples/loop_indexed_053.qr', 'examples/loop_parametric_054.qr',
                    'examples/semantic_index_055.qr')) {
    Write-Host "QRust 0.5.5: $file, five ordinary benchmarks"
    for ($i = 1; $i -le 5; $i++) {
        & $exe bench $file 500
        if ($LASTEXITCODE -ne 0) { throw "benchmark failed: $file" }
    }
    Write-Host "QRust 0.5.5: $file, stage breakdown"
    & $exe bench $file 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw "detailed benchmark failed: $file" }
}
Write-Host 'QRust 0.5.5 benchmarks completed.'
