#!/usr/bin/env bash
cd "$(dirname "$0")"
echo "Getting the latest version from GitHub..."
git pull --ff-only || echo "Could not update (offline?). Starting the last downloaded version."
python3 server.py
