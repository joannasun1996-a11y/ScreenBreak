SCREENBREAK - FIXED WINDOWS TEST PACKAGE

1. Extract the ZIP completely.
2. First run: double-click "Setup ScreenBreak.bat". It requires Python 3.11
   (64-bit) and installs the packages in requirements.txt.
3. Later runs: double-click "Run ScreenBreak.bat".

FIXES
- Repaired an incomplete camera-toggle function that made screenbreak.py invalid
  Python and prevented the windows from opening.
- Camera preview is an independent Tk window. Its X closes only the preview.
  The main ScreenBreak status window remains open.
- Use "Show camera preview" to reopen the preview.
- If the webcam cannot be read, the app does not count the unknown camera state
  as away time during a required break.
- Run ScreenBreak.bat shows startup errors rather than hiding them.

This is a Python test package, not a standalone EXE installer. Webcam processing
is local; video is not recorded or uploaded. Gaze estimates can be imperfect.
