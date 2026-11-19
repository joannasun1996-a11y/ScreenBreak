SCREENBREAK — WINDOWS INSTALLER

Install:
1. Open the ScreenBreak GitHub repository.
2. Click “Download ScreenBreak for Windows” in the README.
3. Run ScreenBreak-Setup.exe and follow the installer.

The Windows installer contains ScreenBreak and its required Python packages.
Python, pip, and a separate package installation are not needed. It is a
64-bit Windows installer. The installer can create a desktop shortcut and
launch ScreenBreak.

ScreenBreak processes webcam frames on the computer. It does not upload webcam
video. Allow camera access in Windows privacy settings when asked. Settings and
progress are stored in the current user's %LOCALAPPDATA%\ScreenBreak folder.

Reports are sent only when the user enters a recipient address and clicks
“Send report now”. Scheduled email sending is disabled. Email delivery requires
a Google Apps Script service connection; see
ScreenBreak\GOOGLE-CLOUD-EMAIL-SETUP.md.

The installer is unsigned, so Windows SmartScreen may display a warning.