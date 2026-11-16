$ErrorActionPreference = 'Stop'
$pythonw = (py -3.11 -c "import sys, pathlib; print(pathlib.Path(sys.executable).with_name('pythonw.exe'))").Trim()
if (-not (Test-Path -LiteralPath $pythonw)) { throw "pythonw.exe not found. Install Python 3.11." }
$script = Join-Path $PSScriptRoot 'screenbreak.py'
$startup = [Environment]::GetFolderPath('Startup')
$link = Join-Path $startup 'ScreenBreak.lnk'
$shell = New-Object -ComObject WScript.Shell
$shortcut = $shell.CreateShortcut($link)
$shortcut.TargetPath = $pythonw
$shortcut.Arguments = '"' + $script + '"'
$shortcut.WorkingDirectory = $PSScriptRoot
$shortcut.Description = 'Start ScreenBreak when you sign in'
$shortcut.Save()
