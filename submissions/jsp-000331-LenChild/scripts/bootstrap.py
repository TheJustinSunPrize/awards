#!/usr/bin/env python3
"""Fetch pinned external proof sources into the ignored .lake directory."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import urllib.request

PACKAGE = Path(__file__).resolve().parents[1]
ROOT = PACKAGE / ".lake" / "upstream"
LOCK = PACKAGE / "source-lock.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def within_root(relative: str) -> Path:
    target = (ROOT / relative).resolve()
    if not target.is_relative_to(ROOT.resolve()):
        raise ValueError(f"Path outside source cache: {relative}")
    return target


def verify_sources() -> None:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    for relative, expected in lock["sources"].items():
        path = within_root(relative)
        if not path.is_file() or digest(path) != expected:
            raise RuntimeError(f"Proof source checksum mismatch: {relative}")
    print(f"Verified {len(lock['sources'])} pinned proof source files.", flush=True)


def main() -> None:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    ROOT.mkdir(parents=True, exist_ok=True)
    for asset in lock["assets"]:
        path = within_root(asset["path"])
        if not path.is_file() or digest(path) != asset["sha256"]:
            print(f"Downloading {asset['url']}", flush=True)
            with urllib.request.urlopen(asset["url"], timeout=120) as response:
                data = response.read()
            if hashlib.sha256(data).hexdigest() != asset["sha256"]:
                raise RuntimeError(f"Download checksum mismatch: {asset['url']}")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)

    # Extract only the dependency subtree and its license. Never extract links.
    archive = within_root("downloads/formalpantheon.tar.gz")
    prefix = "FormalPantheon-" + lock["boundedgaps_commit"]
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar.getmembers():
            parts = member.name.split("/")
            if not member.isfile() or len(parts) < 2 or parts[0] != prefix:
                continue
            relative = "/".join(parts[1:])
            if parts[1] != "BoundedGaps" and relative != "LICENSE":
                continue
            target = within_root("FormalPantheon/" + relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            stream = tar.extractfile(member)
            if stream is None:
                raise RuntimeError(f"Cannot extract {member.name}")
            target.write_bytes(stream.read())

    dependency = within_root("FormalPantheon")
    # An isolated Git repository is essential: otherwise git apply can silently
    # skip paths when invoked below an enclosing, unrelated repository root.
    subprocess.run(["git", "init", "--quiet", str(dependency)], check=True)
    for name in (
        "formalpantheon-v4.33.0.patch",
        "formalpantheon-v4.33.0-s2.patch",
        "boundedgaps-linter-v4.33.0.patch",
    ):
        patch = within_root("proof/patches/" + name)
        for args in (["--check"], []):
            subprocess.run(
                ["git", "apply", *args, str(patch)], cwd=dependency, check=True
            )
    verify_sources()


if __name__ == "__main__":
    main()
