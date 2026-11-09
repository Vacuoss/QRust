$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
& cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'Release compilation failed; refusing to benchmark an old executable.' }
$bin = Join-Path (Get-Location) 'target\release\qrust.exe'
foreach ($source in @('examples/core_gates.qr', 'examples/function_stress.qr', 'examples/runtime_while.qr')) {
    & $bin ir-stats $source
    if ($LASTEXITCODE -ne 0) { throw "IR stats failed: $source" }
}
Write-Host 'Benchmark A: small circuit, 5 repeated runs'
for ($i=1; $i -le 5; $i++) {
    & $bin bench examples/core_gates.qr 100000
    if ($LASTEXITCODE -ne 0) { throw 'Small benchmark failed' }
}
Write-Host 'Benchmark B: 3001-instruction function stress, 5 repeated runs'
for ($i=1; $i -le 5; $i++) {
    & $bin bench examples/function_stress.qr 200
    if ($LASTEXITCODE -ne 0) { throw 'Function stress benchmark failed' }
}
& $bin bench examples/function_stress.qr 1000 --detailed
if ($LASTEXITCODE -ne 0) { throw 'Detailed benchmark failed' }
