$ErrorActionPreference = 'Stop'
function Run-Step {
    param([string] $Description, [string[]] $Arguments)
    Write-Host "== $Description =="
    & cargo @Arguments
    if ($LASTEXITCODE -ne 0) { throw "cargo failed: $Description ($LASTEXITCODE)" }
}
Run-Step 'unit tests' @('test')
Run-Step 'valid quantum program' @('run','--','check','examples/numeric_lowering.qr')
Run-Step 'OpenQASM build' @('run','--','build','examples/numeric_lowering.qr')
Run-Step 'optimized release build' @('build','--release')
Run-Step 'IR stats' @('run','--release','--','ir-stats','examples/function_stress.qr')
Run-Step 'function expansion benchmark' @('run','--release','--','bench','examples/function_stress.qr','1000','--detailed')
Write-Host '== expected failure: alias checker =='
& cargo run -- check examples/numeric_lowering_error.qr
if ($LASTEXITCODE -eq 0) { throw 'Alias checker did not reject invalid program' }
Write-Host 'Expected invalid program rejected.'
