; Script Inno Setup - Klutter
; Ce fichier est utilise par Creer_Installateur.bat (ne pas deplacer).
#define MyAppName "Klutter"
#define MyAppVersion "1.0"
#define MyAppExeName "Klutter.exe"

[Setup]
AppId={{3C9A5E71-84D2-4B6F-A1E0-7D52C9B8F146}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
DefaultDirName={autopf}\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=installateur
OutputBaseFilename=Installateur_Klutter
SetupIconFile=icone.ico
UninstallDisplayIcon={app}\{#MyAppExeName}
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
; Installation sans droits administrateur par defaut (dossier de l'utilisateur),
; avec la possibilite d'installer pour tous les utilisateurs.
PrivilegesRequired=lowest
PrivilegesRequiredOverridesAllowed=dialog
#if Ver >= EncodeVer(6,3,0)
ArchitecturesInstallIn64BitMode=x64compatible
#else
ArchitecturesInstallIn64BitMode=x64
#endif

[Languages]
#if FileExists(CompilerPath + "Languages\French.isl")
Name: "french"; MessagesFile: "compiler:Languages\French.isl"
#else
Name: "english"; MessagesFile: "compiler:Default.isl"
#endif

[Tasks]
Name: "desktopicon"; Description: "{cm:CreateDesktopIcon}"; GroupDescription: "{cm:AdditionalIcons}"; Flags: unchecked

[Files]
Source: "dist\Klutter\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

[Icons]
Name: "{autoprograms}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "{cm:LaunchProgram,{#StringChange(MyAppName, '&', '&&')}}"; Flags: nowait postinstall skipifsilent
