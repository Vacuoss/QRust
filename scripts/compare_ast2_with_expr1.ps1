param([string[]]$Cases = @('bell.qr','core_gates.qr','function_stress.qr','loop_indexed_053.qr','qcu_bell_0511.qr','qcu_feedback_0511.qr','static_loop_control_0513.qr','arena_long_0514.qr'))
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Archive = Join-Path $Root 'reference/QRust_0.5.14_expr_fixed_baseline.zip'
if (-not (Test-Path $Archive)) { throw "Missing baseline archive: $Archive (use full ZIP)" }
$Workspace = Join-Path ([IO.Path]::GetTempPath()) ("qrust-ast-parity-" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $Workspace | Out-Null
try {
    $Extract = Join-Path $Workspace 'baseline'
    Expand-Archive -LiteralPath $Archive -DestinationPath $Extract
    $Base = Join-Path $Extract 'QRust_Core_0.5.14_expr_preview'
    $BaseExe = Join-Path $Workspace 'base-target/release/qrust.exe'
    $NewExe = Join-Path $Root 'target/release/qrust.exe'
    & cargo build --release --manifest-path (Join-Path $Base 'Cargo.toml') --target-dir (Join-Path $Workspace 'base-target')
    if ($LASTEXITCODE -ne 0) { throw 'baseline build failed' }
    & cargo build --release --manifest-path (Join-Path $Root 'Cargo.toml')
    if ($LASTEXITCODE -ne 0) { throw 'new version build failed' }
    foreach ($Case in $Cases) {
        $Original = Join-Path $Root "examples/$Case"
        if (-not (Test-Path $Original)) { throw "missing example: $Original" }
        $Hashes = @{}
        foreach ($Variant in @(@{Name='old';Exe=$BaseExe},@{Name='new';Exe=$NewExe})) {
            $Directory = Join-Path $Workspace $Variant.Name
            New-Item -ItemType Directory -Force $Directory | Out-Null
            $Source = Join-Path $Directory $Case
            Copy-Item -LiteralPath $Original -Destination $Source
            & $Variant.Exe build $Source
            if ($LASTEXITCODE -ne 0) { throw "QASM failed ($Case / $($Variant.Name))" }
            & $Variant.Exe build-qcu $Source
            if ($LASTEXITCODE -ne 0) { throw "QCU failed ($Case / $($Variant.Name))" }
            foreach ($Ext in @('qasm','qcu')) {
                $Output = [IO.Path]::ChangeExtension($Source, $Ext)
                $Hashes["$($Variant.Name):$Ext"] = (Get-FileHash -LiteralPath $Output -Algorithm SHA256).Hash
            }
        }
        foreach ($Ext in @('qasm','qcu')) {
            if ($Hashes["old:$Ext"] -ne $Hashes["new:$Ext"]) { throw "BYTE MISMATCH: $Case ($Ext)" }
            Write-Host "MATCH: $Case ($Ext)"
        }
    }
    Write-Host "PASS: $($Cases.Count) cases, both OpenQASM and QCU byte-identical"
} finally { Remove-Item -LiteralPath $Workspace -Force -Recurse -ErrorAction SilentlyContinue }
