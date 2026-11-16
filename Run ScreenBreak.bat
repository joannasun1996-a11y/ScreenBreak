@echo off
setlocal
cd /d "%~dp0"
py -3.11 "%~dp0screenbreak.py"
if errorlevel 1 (
  echo.
  echo ScreenBreak stopped with an error.
  pause
)
