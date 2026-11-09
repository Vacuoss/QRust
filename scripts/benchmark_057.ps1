param([int]$MaxPeakMiB = 1024)
$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/core_gates.qr', 'examples/function_stress.qr',
                    'examples/loop_indexed_053.qr', 'examples/loop_parametric_054.qr')) {
    Write-Host "QRust 0.5.7: checking $file"
    & $exe bench $file 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw "stage benchmark failed: $file" }
    Write-Host 'End-to-end measurement (read, compile, emit, write)'
    & $exe bench-e2e $file 5
    if ($LASTEXITCODE -ne 0) { throw "end-to-end benchmark failed: $file" }
    Write-Host 'Emitter time attribution (profiling overhead included)'
    & $exe bench-e2e $file 2 --emit-profile
    if ($LASTEXITCODE -ne 0) { throw "emitter profiling failed: $file" }
}
foreach ($count in @(10000, 100000, 500000)) {
    Write-Host "QRust 0.5.7 stress: $count IR instructions; peak memory budget $MaxPeakMiB MiB"
    & $exe bench-stress $count $MaxPeakMiB
    if ($LASTEXITCODE -ne 0) { throw "stress or memory budget failed: $count" }
}
Write-Host 'QRust 0.5.7 benchmark suite completed.'
