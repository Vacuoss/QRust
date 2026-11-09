# QRust compact test runner. No test is skipped or suppressed
param(
    [switch]$Full,
    [switch]$Release
)
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    $arguments = @('test')
    if ($Release) { $arguments += '--release' }
    if ($Full) {
        & cargo @arguments
    } else {
        & cargo @arguments -- --quiet
    }
    $code = $LASTEXITCODE
    if ($code -ne 0) { throw "QRust cargo test failed (exit $code)" }
} finally {
    Pop-Location
}
