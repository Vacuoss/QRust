$ErrorActionPreference = 'Stop'
cargo build --release
if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
foreach ($Source in @('examples/function_stress.qr', 'examples/loop_indexed_053.qr')) {
    & '.\target\release\qrust.exe' bench-qasm $Source 25
    if ($LASTEXITCODE -ne 0) { throw "QASM benchmark failed: $Source" }
}
& '.\target\release\qrust.exe' bench-stress 500000 1024
if ($LASTEXITCODE -ne 0) { throw 'String stress failed' }
& '.\target\release\qrust.exe' bench-stress-stream 500000 1024
if ($LASTEXITCODE -ne 0) { throw 'Stream stress failed' }
Write-Host 'Benchmark complete (compile/write times depend on the filesystem).'
