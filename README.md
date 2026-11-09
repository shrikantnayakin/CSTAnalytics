# CST Analytics

Runs on your own computer. Your Salesforce login, access settings and downloaded case data
stay on this PC (they are listed in `.gitignore`, so they are never uploaded to GitHub).

## First time
1. Install Python 3 and Git.
2. `git clone <your-private-repo-url>` and open the folder.

## Every day
- Windows: double-click `start-windows.bat`
- Mac/Linux: run `./start.sh`

It downloads the latest version from GitHub, then starts the app at http://127.0.0.1:8000
Check the running version at http://127.0.0.1:8000/api/version

## Updating (when you change the code)
`git add index.html server.py` → `git commit -m "message"` → `git push`
Before pushing, run `git status` and make sure no private file is listed.
