$ErrorActionPreference = 'Stop'
$root=Split-Path -Parent $PSScriptRoot
Push-Location $root
try {
    cargo test -- --quiet
    if ($LASTEXITCODE -ne 0) { throw 'QRust unit/integration tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'QRust release build failed' }
    $exe=Join-Path $root 'target\release\qrust.exe'
    & $exe check-host (Join-Path $root 'examples\functions_0616.qr')
    if ($LASTEXITCODE -ne 0) { throw 'function static check failed' }
    $out=& $exe run-host (Join-Path $root 'examples\functions_0616.qr') --seed 42 --backend local
    if ($LASTEXITCODE -ne 0) { throw 'function runtime failed' }
    $outText=$out -join "`n"
    if ($outText -notmatch 'measurement:\s*[01]') { throw "function execution missing measurement: $outText" }
    Write-Output $out
    & $exe check-host (Join-Path $root 'examples\borrow_stress_0616.qr')
    if ($LASTEXITCODE -ne 0) { throw 'borrow stress static check failed' }
    & $exe bench-host-check (Join-Path $root 'examples\borrow_stress_0616.qr') 30
    if ($LASTEXITCODE -ne 0) { throw 'borrow benchmark failed' }
    $coin=Join-Path $root 'examples\hybrid_coin_flip_0614.qr'
    $coins=& $exe run-host $coin --seed 42 --input 100
    if ($LASTEXITCODE -ne 0 -or (($coins -join "`n") -notmatch '(?m)^\s*Total:\s*100\s*$')) {
        throw "coin smoke failed: $($coins -join ' | ')"
    }
    $bell=& $exe run (Join-Path $root 'examples\bell.qr') --shots 16 --seed 42
    if ($LASTEXITCODE -ne 0 -or (($bell -join "`n") -notmatch '(?m)^\s*00\s+')) { throw 'Bell smoke failed' }
    Write-Output 'QRust hybrid verification complete'
} finally { Pop-Location }
