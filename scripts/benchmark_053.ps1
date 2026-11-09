$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'Release build failed; refusing stale benchmark executable' }
$exe = Join-Path (Get-Location) 'target\release\qrust.exe'
Write-Host 'QRust 0.5.3 - small circuit (five runs)'
for ($i=1; $i -le 5; $i++) {
    & $exe bench examples/core_gates.qr 100000
    if ($LASTEXITCODE -ne 0) { throw 'Small benchmark failed' }
}
Write-Host 'QRust 0.5.3 - prepared function stress, 3001 gates (five runs)'
for ($i=1; $i -le 5; $i++) {
    & $exe bench examples/function_stress.qr 500
    if ($LASTEXITCODE -ne 0) { throw 'Function benchmark failed' }
}
Write-Host 'QRust 0.5.3 - stage breakdown'
& $exe bench examples/function_stress.qr 1000 --detailed
if ($LASTEXITCODE -ne 0) { throw 'Detailed benchmark failed' }
Write-Host 'QRust 0.5.3 - indexed loop must use the regular path'
& $exe bench examples/loop_indexed_053.qr 500 --detailed
if ($LASTEXITCODE -ne 0) { throw 'Indexed loop benchmark failed' }
Write-Host 'QRust 0.5.3 benchmarks complete.'
