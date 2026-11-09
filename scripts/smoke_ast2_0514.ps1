$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'unit tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    # Child .ps1 scripts signal failures with terminating errors (throw)
    # LASTEXITCODE belongs to the last native executable, not the child script
    & (Join-Path $PSScriptRoot 'smoke_expr_0514.ps1')
    & (Join-Path $PSScriptRoot 'compare_ast2_with_expr1.ps1')
    Write-Host 'QRust AST.2 preview smoke passed.'
} finally { Pop-Location }
