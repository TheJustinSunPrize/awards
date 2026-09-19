#!/usr/bin/env python3
"""Fetch and verify the unchanged, explicitly credited finite proof."""
import argparse
import hashlib
import json
from pathlib import Path
import urllib.request

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check-only", action="store_true", help="Require an existing local source.")
args = parser.parse_args()
manifest = json.loads((root / "source-manifest.json").read_text())
for entry in manifest["files"]:
    destination = root / entry["path"]
    if destination.exists():
        data = destination.read_bytes()
    else:
        if args.check_only:
            raise SystemExit(f"Missing source: {entry['path']}")
        url = (manifest["repository"].replace("https://github.com/",
                                             "https://raw.githubusercontent.com/")
               + "/" + manifest["commit"] + "/" + entry["upstream_path"])
        with urllib.request.urlopen(url, timeout=60) as response:
            data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if len(data) != entry["bytes"] or digest != entry["sha256"]:
        raise SystemExit(f"Source identity mismatch: {entry['path']}")
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    print(f"Verified {entry['path']}: {len(data)} bytes, SHA-256 {digest}")
