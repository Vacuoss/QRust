$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$Fixture = Join-Path $Root 'reference/QRust_0.5.14_ast2_stable_source.zip'
if (-not (Test-Path $Fixture)) { throw 'stable baseline archive is missing' }
$Tmp = Join-Path $env:TEMP ("qrust-static-diff-" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Tmp | Out-Null
try {
    $Baseline = Join-Path $Tmp 'old'
    Expand-Archive -LiteralPath $Fixture -DestinationPath $Baseline
    Push-Location $Baseline
    try {
        cargo build --release
        if ($LASTEXITCODE -ne 0) { throw 'baseline build failed' }
    } finally { Pop-Location }
    Push-Location $Root
    try {
        cargo build --release
        if ($LASTEXITCODE -ne 0) { throw 'new build failed' }
    } finally { Pop-Location }
    $OldExe = Join-Path $Baseline 'target/release/qrust.exe'
    $NewExe = Join-Path $Root 'target/release/qrust.exe'
    if (-not (Test-Path $OldExe)) { $OldExe = Join-Path $Baseline 'target/release/qrust' }
    if (-not (Test-Path $NewExe)) { $NewExe = Join-Path $Root 'target/release/qrust' }
    foreach ($Name in @('bell', 'core_gates', 'function_stress', 'loop_indexed_053', 'static_loop_control_0513')) {
        $Path = Join-Path $Root "examples/$Name.qr"
        foreach ($Version in @('old', 'new')) {
            $Folder = Join-Path $Tmp "$Version-output"
            New-Item -ItemType Directory -Path $Folder -Force | Out-Null
            $File = Join-Path $Folder "$Name.qr"
            Copy-Item -LiteralPath $Path -Destination $File -Force
            $Exe = if ($Version -eq 'old') { $OldExe } else { $NewExe }
            & $Exe build $File | Out-Null
            if ($LASTEXITCODE -ne 0) { throw "$Name $Version QASM failed" }
            & $Exe build-qcu $File | Out-Null
            if ($LASTEXITCODE -ne 0) { throw "$Name $Version QCU failed" }
        }
        foreach ($Ext in @('qasm','qcu')) {
            $A=(Get-FileHash (Join-Path $Tmp "old-output/$Name.$Ext") -Algorithm SHA256).Hash
            $B=(Get-FileHash (Join-Path $Tmp "new-output/$Name.$Ext") -Algorithm SHA256).Hash
            if ($A -ne $B) {throw "$Name.$Ext does not match 0.5.14-ast.2"}
            Write-Host "MATCH: $Name.$Ext (SHA-256 $B)"
        }
    }
    Write-Host 'PASS: 5 programs, QASM and QCU byte-identical to 0.5.14-ast.2'
} finally {
    Remove-Item -LiteralPath $Tmp -Recurse -Force -ErrorAction SilentlyContinue
}
