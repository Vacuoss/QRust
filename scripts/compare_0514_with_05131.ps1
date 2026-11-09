param([string[]]$Cases = @('bell.qr','core_gates.qr','function_stress.qr','loop_indexed_053.qr','qcu_bell_0511.qr','qcu_feedback_0511.qr','static_loop_control_0513.qr'))
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Archive=Join-Path $Root 'reference/QRust_0.5.13.1_baseline.zip'
if (-not (Test-Path $Archive)) { throw "Missing baseline: $Archive. Use full distribution, not compact source ZIP." }
$Workspace=Join-Path ([System.IO.Path]::GetTempPath()) ("qrust-compare-"+[Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $Workspace | Out-Null
try {
    $Expand=Join-Path $Workspace 'baseline'
    Expand-Archive -LiteralPath $Archive -DestinationPath $Expand
    $Base=Join-Path $Expand 'QRust_Core_0.5.13.1'
    $BaselineExe=Join-Path $Workspace 'baseline-target/release/qrust.exe'
    $CurrentExe=Join-Path $Root 'target/release/qrust.exe'
    cargo build --release --manifest-path (Join-Path $Base 'Cargo.toml') --target-dir (Join-Path $Workspace 'baseline-target')
    if ($LASTEXITCODE -ne 0) { throw 'baseline release build failed' }
    Push-Location $Root
    try { cargo build --release; if ($LASTEXITCODE -ne 0) { throw 'candidate release build failed' } }
    finally { Pop-Location }
    $Groups = @('baseline-output','current-output')
    foreach ($Group in $Groups) { New-Item -ItemType Directory -Force (Join-Path $Workspace $Group) | Out-Null }
    foreach ($Name in $Cases) {
        $Src=Join-Path $Root "examples/$Name"
        if (-not (Test-Path $Src -PathType Leaf)) { throw "missing source case: $Src" }
        foreach ($Item in @(@{Exec=$BaselineExe;Dir='baseline-output'},@{Exec=$CurrentExe;Dir='current-output'})) {
            $File=Join-Path (Join-Path $Workspace $Item.Dir) $Name
            Copy-Item -LiteralPath $Src -Destination $File
            & $Item.Exec build $File
            if ($LASTEXITCODE -ne 0) { throw "QASM build failed: $Name on $($Item.Dir)" }
            & $Item.Exec build-qcu $File
            if ($LASTEXITCODE -ne 0) { throw "QCU build failed: $Name on $($Item.Dir)" }
        }
        foreach ($Extension in @('qasm','qcu')) {
            $Short=[IO.Path]::ChangeExtension($Name,$Extension)
            $A=Join-Path $Workspace "baseline-output/$Short"
            $B=Join-Path $Workspace "current-output/$Short"
            $HashA=(Get-FileHash -Algorithm SHA256 -LiteralPath $A).Hash
            $HashB=(Get-FileHash -Algorithm SHA256 -LiteralPath $B).Hash
            if ($HashA -ne $HashB) { throw "BYTE MISMATCH: $Short - baseline=$HashA candidate=$HashB" }
            Write-Host "MATCH: $Short (SHA-256: $HashA)"
        }
    }
    Write-Host "PASS: all $($Cases.Count) cases have byte-identical QASM and QCU"
} finally {
    Remove-Item -LiteralPath $Workspace -Recurse -Force -ErrorAction SilentlyContinue
}
