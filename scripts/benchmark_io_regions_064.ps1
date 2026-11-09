param(
  [int]$Runs = 100,
  [int]$RegionIterations = 1000,
  [string]$OutDir = 'benchmark_results',
  [string]$BaselineExe = ''
)
$ErrorActionPreference = 'Stop'
if ($Runs -lt 1 -or $Runs -gt 1000) { throw 'Runs must be 1..1000' }
if ($RegionIterations -lt 1 -or $RegionIterations -gt 100000) { throw 'RegionIterations must be 1..100000' }
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$exe = Join-Path $root 'target\release\qrust.exe'
if (!(Test-Path $exe)) { throw "Missing $exe; run cargo build --release" }
$output = Join-Path $root $OutDir
New-Item -ItemType Directory -Force $output | Out-Null
$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$report = Join-Path $output "io-region-064-$stamp.txt"
$sizeCsv = Join-Path $output "binary-064-$stamp.csv"
$exeInfo = Get-Item $exe
$sizeRows = @([pscustomobject]@{ Edition='QRust-0.6.4'; Bytes=$exeInfo.Length; MiB=[math]::Round($exeInfo.Length/1MB, 4) })
if ($BaselineExe) {
  if (!(Test-Path $BaselineExe)) { throw "Baseline not found: $BaselineExe" }
  $baselineItem=Get-Item $BaselineExe
  $sizeRows+= [pscustomobject]@{ Edition='Baseline'; Bytes=$baselineItem.Length; MiB=[math]::Round($baselineItem.Length/1MB,4) }
}
$compact = Join-Path $root 'target\compact\qrust.exe'
if (Test-Path $compact) {
  $compactItem=Get-Item $compact
  $sizeRows+= [pscustomobject]@{ Edition='QRust-0.6.4-compact'; Bytes=$compactItem.Length; MiB=[math]::Round($compactItem.Length/1MB,4) }
}
$sizeRows | Export-Csv -Path $sizeCsv -NoTypeInformation -Encoding UTF8
function Run-Case([string]$title,[string]$binary,[string[]]$parameters) {
  "`n===== $title =====" | Tee-Object -FilePath $report -Append
  $text = & $binary @parameters 2>&1 | Out-String
  $text | Tee-Object -FilePath $report -Append
  if ($LASTEXITCODE -ne 0) { throw "$title exited with code $LASTEXITCODE" }
}
$fixture = Join-Path $root 'benchmark_fixtures\function_stress.qr'
$cfg = Join-Path $root 'benchmark_fixtures\reference_nll_0523.qr'
$cfgBranch = Join-Path $root 'benchmark_fixtures\reference_cfg_branch_0523.qr'
Run-Case 'Current fresh end-to-end' $exe @('bench-e2e',$fixture,$Runs)
Run-Case 'Current persistent end-to-end' $exe @('bench-e2e',$fixture,$Runs,'--persistent')
Run-Case 'Current OS file I/O phases' $exe @('bench-io-phases',$fixture,$Runs)
Run-Case 'Current region-only NLL' $exe @('bench-regions',$cfg,$RegionIterations)
Run-Case 'Current region-only CFG branch' $exe @('bench-regions',$cfgBranch,$RegionIterations)
Run-Case 'Current region-only function stress' $exe @('bench-regions',$fixture,$RegionIterations)
if ($BaselineExe) {
  Run-Case 'Baseline end-to-end' $BaselineExe @('bench-e2e',$fixture,$Runs)
  Run-Case 'Baseline compiler-only' $BaselineExe @('bench',$cfg,$RegionIterations)
  Run-Case 'Current compiler-only' $exe @('bench',$cfg,$RegionIterations)
}
Write-Host "Report: $report"
Write-Host "Executable sizes: $sizeCsv"
