param([int]$Iterations = 3)
$ErrorActionPreference='Stop'
$Root=(Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo test
    if ($LASTEXITCODE -ne 0) { throw 'unit tests failed' }
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe=Join-Path $Root 'target/release/qrust.exe'
    $Dir=Join-Path ([IO.Path]::GetTempPath()) ('qrust-expr-'+[guid]::NewGuid().ToString('N'))
    New-Item -ItemType Directory $Dir | Out-Null
    try {
        $Long='let q=qubit();rx('+('1+'*20000)+'1,q);'
        $Short='let q=qubit();rx(1+2*3-4/2,q);'
        foreach ($Case in @(@{Name='binary-20k';Source=$Long},@{Name='small-precedence';Source=$Short})) {
            $File=Join-Path $Dir ($Case.Name+'.qr')
            [IO.File]::WriteAllText($File,$Case.Source,[Text.UTF8Encoding]::new($false))
            $Out=& $Exe check $File 2>&1
            if ($LASTEXITCODE -ne 0) { throw "long expression rejected: $Out" }
            Write-Host "PASS: $($Case.Name) - $Out"
        }
        foreach ($Case in @('deep-unary','deep-parentheses')) {
            $Bad=if ($Case -eq 'deep-unary') { 'let q=qubit();rx('+('-'*400)+'1,q);' } else { 'let q=qubit();rx('+('('*400)+'1'+(')'*400)+',q);' }
            $File=Join-Path $Dir ($Case+'.qr')
            [IO.File]::WriteAllText($File,$Bad,[Text.UTF8Encoding]::new($false))
            $ErrorActionPreference='Continue'; $Out=& $Exe check $File 2>&1; $Exit=$LASTEXITCODE; $ErrorActionPreference='Stop'
            if ($Exit -eq 0 -or (($Out|Out-String) -notmatch 'parser recursion limit')) { throw "unexpected result for $Case : $Out" }
            Write-Host "PASS: $Case returned a diagnostic"
        }
        # Expected negative tests leave LASTEXITCODE=1 even though they passed
        # Nested PowerShell scripts inherit this state; clear it only after ALL checks pass
        $global:LASTEXITCODE = 0
        Write-Host 'PASS: QRust expression smoke completed'
    } finally { Remove-Item -LiteralPath $Dir -Recurse -Force }
} finally { Pop-Location }
