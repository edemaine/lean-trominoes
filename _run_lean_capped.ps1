param(
  [Parameter(Mandatory = $true)] [string] $Source,
  [Parameter(Mandatory = $true)] [string] $Output,
  [Parameter(Mandatory = $true)] [string] $LakeExecutable
)
$ErrorActionPreference = 'Stop'
$existing = Get-CimInstance Win32_Process |
  Where-Object { $_.Name -in @('lean.exe', 'lake.exe') }
if ($existing) { Write-Error 'Lean/Lake process already running'; exit 2 }
$env:LEAN_NUM_THREADS = '1'
$outLog = [IO.Path]::GetTempFileName()
$errLog = [IO.Path]::GetTempFileName()
try {
  $arguments = @('env', 'lean', '-j', '1',
    '-DrelaxedAutoImplicit=false', '-o', $Output, $Source)
  $startArguments = @{
    FilePath = $LakeExecutable
    ArgumentList = $arguments
    WorkingDirectory = $PSScriptRoot
    RedirectStandardOutput = $outLog
    RedirectStandardError = $errLog
    WindowStyle = 'Hidden'
    PassThru = $true
  }
  $process = Start-Process @startArguments
  if (-not $process.WaitForExit(60000)) {
    & taskkill.exe /PID $process.Id /T /F | Out-Null
    $exitCode = 124
  } else {
    $process.WaitForExit()
    $exitCode = $process.ExitCode
  }
  if ((Get-Item $outLog).Length -gt 0) { Get-Content -Raw $outLog }
  if ((Get-Item $errLog).Length -gt 0) {
    [Console]::Error.Write((Get-Content -Raw $errLog))
  }
  exit $exitCode
} finally {
  Remove-Item -LiteralPath $outLog, $errLog `
    -Force -ErrorAction SilentlyContinue
}
