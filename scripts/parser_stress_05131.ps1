param([int]$Iterations = 3)
$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Push-Location $Root
try {
    cargo build --release
    if ($LASTEXITCODE -ne 0) { throw 'release build failed' }
    $Exe = Join-Path $Root 'target/release/qrust.exe'
    $TempDir = Join-Path ([System.IO.Path]::GetTempPath()) ([Guid]::NewGuid().ToString('N'))
    New-Item -ItemType Directory $TempDir | Out-Null
    function Verify-Case([string]$Name, [string]$Source, [bool]$ExpectedSuccess) {
        $File = Join-Path $TempDir "$Name.qr"
        [System.IO.File]::WriteAllText($File,$Source,[System.Text.UTF8Encoding]::new($false))
        for ($i=0; $i -lt $Iterations; $i++) {
            $Watch = [System.Diagnostics.Stopwatch]::StartNew()
            # Native stderr is expected for rejected inputs; avoid PS 5.1
            # treating redirected stderr as terminating ErrorRecord
            $ErrorActionPreference = 'Continue'
            $Output = & $Exe check $File 2>&1
            $Status = $LASTEXITCODE
            $ErrorActionPreference = 'Stop'
            $Watch.Stop()
            if (($Status -eq 0) -ne $ExpectedSuccess) { throw "$Name unexpected exit $Status : $Output" }
            if (-not $ExpectedSuccess) {
                if (-not (($Output | Out-String) -match '(parser recursion limit|binary expression chain limit|nested block scope limit)')) {
                    throw "$Name failed for unexpected reason: $Output"
                }
            }
            Write-Host "$Name [$i]: $($Watch.Elapsed.TotalMilliseconds.ToString('F2')) ms exit=$Status"
        }
    }
    try {
        Verify-Case 'deep-parentheses' ('let q=qubit();rx('+('('*500)+'1'+(')'*500)+',q);') $false
        Verify-Case 'deep-unary' ('let q=qubit();rx('+('-'*500)+'1,q);') $false
        Verify-Case 'deep-binary' ('let q=qubit();rx('+('1+'*20000)+'1,q);') $true
        Verify-Case 'deep-calls' ('let q=qubit();rx('+('sin('*500)+'1'+(')'*500)+',q);') $false
        Verify-Case 'deep-blocks' (('{'*200)+'let q=qubit();'+('}'*200)) $false
        $Flat = 'let q=qubit();' + ('h(q);'*10000)
        Verify-Case 'flat-ten-thousand' $Flat $true
        $Nested = 'let q=qubit();rx(sin((pi/2))+cos((pi/3)),q);'
        Verify-Case 'normal-nested' $Nested $true
    } finally { Remove-Item -LiteralPath $TempDir -Recurse -Force }
} finally { Pop-Location }
