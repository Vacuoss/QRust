$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/core_gates.qr','examples/function_stress.qr','examples/loop_indexed_053.qr','examples/loop_parametric_054.qr')) {
    Write-Host "Benchmark $file"
    for ($i=1;$i -le 5;$i++) {
        & $exe bench $file 500
        if ($LASTEXITCODE -ne 0) { throw "bench failed: $file" }
    }
    & $exe bench $file 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw "detailed bench failed: $file" }
}
Write-Host 'QRust 0.5.4 benchmarks complete.'
