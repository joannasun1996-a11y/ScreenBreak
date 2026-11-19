# ScreenBreak

## Install on Windows

**[Download ScreenBreak for Windows](https://github.com/joannasun1996-a11y/ScreenBreak/releases/latest/download/ScreenBreak-Setup.exe)**

Download ScreenBreak-Setup.exe and open it. The installer includes ScreenBreak and its Python dependencies; Python and pip do not need to be installed separately. This build is for 64-bit Windows.

The installer offers a desktop shortcut and starts ScreenBreak after installation. ScreenBreak can be removed from Windows Settings > Apps.

## Email reports

Reports are sent only when you enter a recipient email and click **Send report now**. There is no automatic email schedule. A Google Apps Script service connection is needed to send email; see [manual email setup](ScreenBreak/GOOGLE-CLOUD-EMAIL-SETUP.md). Keep the service URL and access key private.

## Download troubleshooting

The latest installer is published after a successful GitHub Actions build. If the download link has no file yet, open the [Actions page](https://github.com/joannasun1996-a11y/ScreenBreak/actions) and check the newest build. The installer is unsigned, so Windows may show a SmartScreen warning.