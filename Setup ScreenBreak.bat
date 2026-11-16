@echo off
setlocal
cd /d "%~dp0"
echo ==========================================
echo       ScreenBreak - First-time setup
echo ==========================================
echo.
echo This setup installs the Python packages ScreenBreak needs.
echo It does not change or upload your webcam video.
echo.
py -3.11 --version >nul 2>&1
if errorlevel 1 (
  echo Python 3.11 was not found.
  echo Please install Python 3.11 64-bit, then run this setup again.
  echo https://www.python.org/downloads/release/python-3119/
  pause
  exit /b 1
)
echo Installing required packages...
py -3.11 -m pip install --user -r requirements.txt
if errorlevel 1 (
  echo Package installation failed.
  pause
  exit /b 1
)
echo Setting ScreenBreak to start when you sign in...
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0Install-Startup.ps1"
if errorlevel 1 (
  echo Startup setup failed. You can still run ScreenBreak manually.
  pause
  exit /b 1
)
echo.
echo Setup complete. Starting ScreenBreak...
start "ScreenBreak" cmd /k ""%~dp0Run ScreenBreak.bat""
echo You can close this setup window.
timeout /t 3 >nul
