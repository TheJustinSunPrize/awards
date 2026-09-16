#!/usr/bin/env python3
"""Check the byte identity of the vendored, attributed source files."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "vendor-manifest.json").read_text())
entries = manifest["files"] + [manifest["formal_conjectures"]]
for item in entries:
    data = (root / item["path"]).read_bytes()
    if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
        raise SystemExit(f"Source identity mismatch: {item['path']}")
print(f"Verified byte counts and SHA-256 for {len(entries)} attributed source files.")
