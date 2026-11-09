param([int]$Iterations=500)
$ErrorActionPreference = 'Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo build --release
    if($LASTEXITCODE -ne 0){throw 'release build failed'}
    $Exe=Join-Path $Root 'target/release/qrust.exe'
    if(-not(Test-Path $Exe)){$Exe=Join-Path $Root 'target/release/qrust'}
    $Output=Join-Path $Root 'benchmark_results';New-Item -ItemType Directory -Path $Output -Force|Out-Null
    $Log=Join-Path $Output ('typed-0516-'+(Get-Date -Format yyyyMMdd-HHmmss)+'.txt')
    foreach($Name in @('core_gates','rust_static_0515','rust_typed_0516')) {
        "### $Name"|Tee-Object -FilePath $Log -Append
        & $Exe bench-stages "examples/$Name.qr" $Iterations | Tee-Object -FilePath $Log -Append
        if($LASTEXITCODE -ne 0){throw "benchmark failed: $Name"}
    }
    Write-Host "Benchmark log: $Log"
} finally {Pop-Location}
