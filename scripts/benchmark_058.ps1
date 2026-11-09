param([int]$MaxPeakMiB = 1024, [int]$IoRuns = 25)
$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($file in @('examples/core_gates.qr', 'examples/function_stress.qr', 'examples/loop_indexed_053.qr')) {
    Write-Host "QRust 0.5.8: $file"
    & $exe bench $file 500 --detailed
    if ($LASTEXITCODE -ne 0) { throw "stage benchmark failed: $file" }
    & $exe bench-e2e $file 15
    if ($LASTEXITCODE -ne 0) { throw "end-to-end benchmark failed: $file" }
    & $exe bench-io $file $IoRuns
    if ($LASTEXITCODE -ne 0) { throw "temp-directory I/O benchmark failed: $file" }
    & $exe bench-io $file $IoRuns --dir .
    if ($LASTEXITCODE -ne 0) { throw "project-directory I/O benchmark failed: $file" }
}
foreach ($count in @(10000, 100000, 500000)) {
    & $exe bench-stress $count $MaxPeakMiB
    if ($LASTEXITCODE -ne 0) { throw "stress or memory budget failed: $count" }
}
Write-Host 'QRust 0.5.8 benchmarks completed.'
