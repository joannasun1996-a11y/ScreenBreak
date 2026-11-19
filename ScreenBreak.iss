#define MyAppName "ScreenBreak"
#define MyAppVersion "2.32"
#define MyAppPublisher "ScreenBreak"
#define MyAppExeName "ScreenBreak.exe"

[Setup]
AppId={{8E6A0C71-6D49-4D2D-9C0D-2C0C9C9A42A1}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={localappdata}\Programs\ScreenBreak
DefaultGroupName=ScreenBreak
UninstallDisplayIcon={app}\{#MyAppExeName}
OutputDir=dist-installer
OutputBaseFilename=ScreenBreak-Setup
ArchitecturesInstallIn64BitMode=x64
PrivilegesRequired=lowest
Compression=lzma2
SolidCompression=yes
WizardStyle=modern

[Files]
Source: "dist\ScreenBreak\*"; DestDir: "{app}"; Flags: recursesubdirs ignoreversion

[Icons]
Name: "{group}\ScreenBreak"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\ScreenBreak"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Additional shortcuts:"

[Registry]
Root: HKCU; Subkey: "Software\Microsoft\Windows\CurrentVersion\Run"; ValueType: string; ValueName: "ScreenBreak"; ValueData: """{app}\{#MyAppExeName}"""; Flags: uninsdeletevalue

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "Launch ScreenBreak"; Flags: postinstall nowait skipifsilent