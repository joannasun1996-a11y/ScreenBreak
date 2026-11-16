SCREENBREAK — STANDALONE WINDOWS INSTALLER BUILD

This project is prepared to build a Windows installer in GitHub Actions.
The person installing ScreenBreak will NOT need to install Python or pip packages.

IMPORTANT:
- The build must run on a Windows GitHub Actions runner.
- The installer is x64 for Windows 11 64-bit.
- This is an unsigned installer. Windows SmartScreen may show a warning because
  the installer has not been code-signed. Do not bypass warnings unless you trust
  the source and have checked the build.
- Webcam access may need to be allowed in Windows Settings > Privacy & security > Camera.
- ScreenBreak processes camera frames locally. It does not upload webcam video.
- User progress is saved under %LOCALAPPDATA%\ScreenBreak.

HOW TO BUILD:
1. Create a new empty repository on GitHub named ScreenBreak.
2. Upload the CONTENTS of this folder to the repository (not the ZIP itself).
3. Make sure the workflow file is at .github/workflows/build-windows.yml.
4. Open the repository's Actions tab.
5. Select "Build ScreenBreak for Windows" and run it, or push to main.
6. Open the completed workflow run, scroll to Artifacts, and download
   ScreenBreak-Windows-Installer.
7. Extract the artifact ZIP. It contains ScreenBreak-Setup.exe.
8. Test the installer on a separate Windows 11 computer before sharing it.

INSTALLING:
Double-click ScreenBreak-Setup.exe and follow the installer. Python is not required.
The installer adds ScreenBreak to the current Windows user's startup at sign-in.
Uninstalling ScreenBreak removes that startup entry.

NOTE:
This workflow is a first packaging attempt, not a claim that the resulting EXE has
already been built or tested. MediaPipe/OpenCV packaging can sometimes require
adjustments after the first cloud build. Test camera startup and gaze detection
on a clean Windows 11 machine before distributing it widely.
