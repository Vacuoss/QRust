# Optional diagnostic of Windows native stdin; the main verification uses
# explicit --input and does not depend on shell pipeline encodings
# This check remains available to diagnose native stdin separately
# Send deterministic bytes directly to native QRust stdin
# Windows PowerShell 5.1 and newer PowerShell releases can use different
# encodings when piping strings to a native executable. Do not use the
# PowerShell object pipeline as a substitute for a byte-level stdin test
function Invoke-QRustSmokeWithStdin {
    param(
        [Parameter(Mandatory = $true)][string]$Executable,
        [Parameter(Mandatory = $true)][string]$SourceFile,
        [ValidateSet('run', 'run-host')][string]$Command = 'run-host',
        [string]$InputLine = '100',
        [uint64]$Seed = 42
    )
    $start = New-Object System.Diagnostics.ProcessStartInfo
    $start.FileName = $Executable
    $start.Arguments = "$Command `"$SourceFile`" --seed $Seed"
    $start.UseShellExecute = $false
    $start.RedirectStandardInput = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.CreateNoWindow = $true

    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $start
    try {
        if (-not $process.Start()) { throw 'Cannot start QRust smoke process' }

        # Raw ASCII + LF: exactly 31 30 30 0A for the default input '100'
        # Bypasses PowerShell's $OutputEncoding and StreamWriter BOM behavior
        $bytes = [System.Text.Encoding]::ASCII.GetBytes($InputLine + "`n")
        $process.StandardInput.BaseStream.Write($bytes, 0, $bytes.Length)
        $process.StandardInput.BaseStream.Flush()
        $process.StandardInput.BaseStream.Close()

        # Drain both pipes asynchronously so neither pipe can block the child
        $stdoutTask = $process.StandardOutput.ReadToEndAsync()
        $stderrTask = $process.StandardError.ReadToEndAsync()
        if (-not $process.WaitForExit(30000)) {
            $process.Kill()
            throw 'QRust native stdin smoke timed out'
        }
        $stdout = $stdoutTask.GetAwaiter().GetResult()
        $stderr = $stderrTask.GetAwaiter().GetResult()
        if ($process.ExitCode -ne 0) {
            throw "QRust native smoke exited with code $($process.ExitCode).`nSTDOUT:`n$stdout`nSTDERR:`n$stderr"
        }
        return $stdout
    } finally {
        $process.Dispose()
    }
}
