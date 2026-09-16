#!/usr/bin/env python3
"""Build the complete theorem and reject unexpected transitive axioms."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from bootstrap import PACKAGE, main as bootstrap, verify_sources

DECLARATIONS = (
    "MediumPNT",
    "Erdos402.erdos_402",
    "JSP331.eventual_graham",
    "JSP331.sufficiently_large_gcd_bound",
    "JSP331.distinct_of_gcd_bound",
    "JSP331.sufficiently_large_distinct_gcd_bound",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def audit_axioms(text: str) -> dict[str, list[str]]:
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    axioms = {name: {a.strip() for a in body.split(",") if a.strip()} for name, body in matches}
    for name in DECLARATIONS:
        if name not in axioms:
            raise RuntimeError(f"Missing axiom audit: {name}")
        if axioms[name] - ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms[name])}")
    return {name: sorted(axioms[name]) for name in DECLARATIONS}


def package_hashes() -> dict[str, str]:
    paths = [PACKAGE / name for name in (
        "JSP331.lean", "Audit.lean", "lakefile.toml", "lake-manifest.json",
        "lean-toolchain", "source-lock.json", "mathlib-cache-roots.json",
    )]
    paths += sorted((PACKAGE / "JSP331").glob("*.lean"))
    paths += sorted((PACKAGE / "scripts").glob("*.py"))
    return {p.relative_to(PACKAGE).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in paths}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bootstrap", action="store_true", help="fetch pinned sources first")
    parser.add_argument("--cache", action="store_true", help="download pinned mathlib artifacts")
    args = parser.parse_args()
    os.environ.setdefault("LEAN_NUM_THREADS", "4")
    output = PACKAGE / "verification-output"
    output.mkdir(exist_ok=True)
    result: dict = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running",
        "commands": [],
    }

    def save() -> None:
        (output / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    def run(command: list[str], filename: str) -> str:
        print("Running: " + " ".join(command), flush=True)
        start = time.monotonic()
        logfile = output / filename
        result["current_command"] = command
        result["current_log"] = filename
        save()
        with logfile.open("w", encoding="utf-8") as log:
            proc = subprocess.Popen(
                command, cwd=PACKAGE, stdout=log, stderr=subprocess.STDOUT,
                encoding="utf-8",
            )
            code = proc.wait()
        data = logfile.read_bytes()
        result["commands"].append({
            "argv": command, "exit_code": code, "seconds": round(time.monotonic() - start, 2),
            "log": filename, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
        })
        result.pop("current_command", None)
        result.pop("current_log", None)
        save()
        text = data.decode("utf-8", errors="replace")
        if code:
            print(text[-6000:], flush=True)
            raise RuntimeError(f"Command failed ({code}); see {logfile}")
        return text

    save()
    try:
        result["phase"] = "source preparation"
        result["package_hashes"] = package_hashes()
        save()
        if args.bootstrap:
            bootstrap()
        verify_sources()
        if shutil.which("lake") is None:
            raise RuntimeError("lake is not on PATH; install elan and the pinned Lean toolchain")
        version = run(["lake", "env", "lean", "--version"], "version.log")
        if "version 4.33.0," not in version:
            raise RuntimeError("Unexpected Lean version")
        result["lean_version"] = version.strip()
        manifest = json.loads((PACKAGE / "lake-manifest.json").read_text(encoding="utf-8"))
        for dependency in manifest["packages"]:
            checkout = PACKAGE / ".lake" / "packages" / dependency["name"]
            revision = run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                           "revision-" + dependency["name"] + ".log").strip()
            if revision != dependency["rev"]:
                raise RuntimeError(f"Unexpected revision for {dependency['name']}")
            run(["git", "-C", str(checkout), "diff", "--exit-code", "HEAD"],
                "clean-" + dependency["name"] + ".log")
        if args.cache:
            result["phase"] = "mathlib cache"
            roots = json.loads((PACKAGE / "mathlib-cache-roots.json").read_text(encoding="utf-8"))
            run(["lake", "exe", "cache", "get", *roots], "cache.log")
        result["phase"] = "complete proof build"
        run(["lake", "build", "JSP331"], "build.log")
        result["phase"] = "transitive axiom audit"
        audit = run(["lake", "env", "lean", "Audit.lean"], "axioms.log")
        result["axioms"] = audit_axioms(audit)
        result["phase"] = "Lean kernel replay"
        run(["lake", "env", "leanchecker", "--fresh", "JSP331.Proof"], "kernel-replay.log")
        verify_sources()
        if package_hashes() != result["package_hashes"]:
            raise RuntimeError("Package sources changed during verification; rerun on stable sources")
        result["status"] = "passed"
        result["phase"] = "complete"
    except Exception as exc:
        result["status"] = "failed"
        result["error"] = str(exc)
        raise
    finally:
        result["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print("Complete theorem build and transitive axiom audit passed.", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
