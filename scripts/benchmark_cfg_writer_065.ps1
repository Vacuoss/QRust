param(
  [int]$Runs = 100,
  [int]$RegionIterations = 3000,
  [string]$BaselineExe = '',
  [string]$OutDir = 'benchmark_results'
)
$ErrorActionPreference = 'Stop'
if ($Runs -lt 1 -or $Runs -gt 1000) { throw 'Runs must be 1..1000' }
if ($RegionIterations -lt 1 -or $RegionIterations -gt 100000) { throw 'RegionIterations must be 1..100000' }
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$exe = Join-Path $root 'target\release\qrust.exe'
if (!(Test-Path $exe)) { throw "Missing $exe (run cargo build --release)" }
$out = Join-Path $root $OutDir
New-Item -ItemType Directory -Force $out | Out-Null
$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$report = Join-Path $out "benchmark-065-$stamp.txt"
function Run([string]$name,[string]$bin,[string[]]$argv) {
  "`n=== $name ===" | Tee-Object -FilePath $report -Append
  $result= & $bin @argv 2>&1 | Out-String
  $result | Tee-Object -FilePath $report -Append
  if ($LASTEXITCODE -ne 0) { throw "$name failed (exit $LASTEXITCODE)" }
}
$region=Join-Path $root 'benchmark_fixtures\reference_nll_0523.qr'
$branch=Join-Path $root 'benchmark_fixtures\reference_cfg_branch_0523.qr'
$stress=Join-Path $root 'benchmark_fixtures\function_stress.qr'
Run '0.6.5 region NLL, no I/O' $exe @('bench-regions',$region,$RegionIterations)
Run '0.6.5 CFG branch, no I/O' $exe @('bench-regions',$branch,$RegionIterations)
Run '0.6.5 function stress, no I/O' $exe @('bench-regions',$stress,$RegionIterations)
Run '0.6.5 persistent QASM end-to-end' $exe @('bench-e2e',$stress,$Runs,'--persistent')
Run '0.6.5 atomic vs fresh filesystem phases' $exe @('bench-io-phases',$stress,$Runs)
if ($BaselineExe) {
  if (!(Test-Path $BaselineExe)) { throw "No baseline EXE: $BaselineExe" }
  Run '0.6.4 baseline region NLL, no I/O' $BaselineExe @('bench-regions',$region,$RegionIterations)
  Run '0.6.4 baseline CFG branch, no I/O' $BaselineExe @('bench-regions',$branch,$RegionIterations)
}
"`n=== Build --skip-unchanged integrity check ===" | Tee-Object -FilePath $report -Append
$folder=Join-Path $out "build-skip-check-$stamp"
New-Item -ItemType Directory -Force $folder | Out-Null
try {
  $src=Join-Path $folder 'test.qr'; $qasm=Join-Path $folder 'test.qasm'
  Copy-Item (Join-Path $root 'benchmark_fixtures\core_gates.qr') $src
  & $exe build $src --force-write | Tee-Object -FilePath $report -Append
  if ($LASTEXITCODE -ne 0) { throw 'Initial build failed' }
  $before=(Get-FileHash $qasm -Algorithm SHA256).Hash
  $beforeTime=(Get-Item $qasm).LastWriteTimeUtc.Ticks
  & $exe build $src --skip-unchanged | Tee-Object -FilePath $report -Append
  if ($LASTEXITCODE -ne 0) { throw 'Skip unchanged build failed' }
  $after=(Get-FileHash $qasm -Algorithm SHA256).Hash
  $afterTime=(Get-Item $qasm).LastWriteTimeUtc.Ticks
  if ($before -ne $after -or $beforeTime -ne $afterTime) { throw 'Skip unchanged modified QASM!' }
  'SHA256 and modification timestamp preserved.' | Tee-Object -FilePath $report -Append
} finally { Remove-Item -Recurse -Force $folder -ErrorAction SilentlyContinue }
$size=[long](Get-Item $exe).Length
"Executable size: $size bytes ($([math]::Round($size/1MB,5)) MiB)" | Tee-Object -FilePath $report -Append
Write-Host "Report: $report"
