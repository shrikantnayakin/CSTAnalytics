@echo off
cd /d "%~dp0"
echo Getting the latest version from GitHub...
git pull --ff-only
if errorlevel 1 echo Could not update (offline?). Starting the last downloaded version.
python server.py
pause
