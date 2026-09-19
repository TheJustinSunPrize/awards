#!/usr/bin/env python3
"""Recompile the submitted source and audit the two top-level theorem axioms.

Requires Python 3.10+, Lean 4.19.0, Lake, and the dependencies pinned in the
included lake-manifest.json. This script does NOT install dependencies, claim
an award, certify an imported library, or establish publication priority.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_LEAN = "4.19.0"
EXPECTED_MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = ("JSP301.known_counterexample", "JSP301.catalog_statement_false")


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-dir", type=Path, default=ROOT / ".verification")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Per-command timeout in seconds (default: 300).")
    parser.add_argument("--also-lake-build", action="store_true",
                        help="Also run the named Lake target; may build dependency targets.")
    args = parser.parse_args()
    log_dir = args.log_dir.resolve()
    log_dir.mkdir(parents=True, exist_ok=True)
    report: dict = {
        "started_utc": utc(),
        "source_sha256": hashlib.sha256((ROOT / "JSP301.lean").read_bytes()).hexdigest(),
        "source_bytes": (ROOT / "JSP301.lean").stat().st_size,
        "platform": {"system": platform.system(), "machine": platform.machine(),
                     "python": platform.python_version()},
        "tests": [], "dependencies": [], "axiom_audit": {}, "all_passed": False,
        "scope": "Local source compilation and axiom audit; not official or independent prize verification.",
        "trust": "Standard Lean import trust. Precompiled dependency artifacts are used; no separately certified independent checker or full imported-library recheck.",
        "network_isolation": "Not asserted by this script. See a separately recorded launcher, if one is used."
    }

    def save() -> None:
        (log_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(name: str, cmd: list[str], expected: int = 0) -> dict:
        start = time.monotonic()
        try:
            proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True,
                                  timeout=args.timeout, check=False)
            code, out, err = proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as exc:
            def text(v: object) -> str:
                return v.decode(errors="replace") if isinstance(v, bytes) else str(v or "")
            code, out, err = 124, text(exc.stdout), text(exc.stderr) + "\nTimed out.\n"
        (log_dir / (name + ".stdout.log")).write_text(out)
        (log_dir / (name + ".stderr.log")).write_text(err)
        row = {"name": name, "command": cmd, "exit_code": code,
               "expected_exit_code": expected, "passed": code == expected,
               "seconds": round(time.monotonic() - start, 6),
               "stdout_file": name + ".stdout.log", "stderr_file": name + ".stderr.log"}
        report["tests"].append(row)
        save()
        print(f"{name}: exit={code}, expected={expected}", flush=True)
        if code != expected:
            raise RuntimeError(f"{name} failed; inspect {log_dir}")
        return {**row, "stdout": out, "stderr": err}

    try:
        for cmd in ("lean", "lake", "git"):
            if not shutil.which(cmd):
                raise RuntimeError(f"Required command not on PATH: {cmd}")
        if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
            raise RuntimeError("Unexpected lean-toolchain file")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        if mathlib["rev"] != EXPECTED_MATHLIB:
            raise RuntimeError("Mathlib revision differs from the verified revision")
        versions = run("01_lean_version", ["lean", "--version"])
        if not re.search(r"version 4\.19\.0(?:[,\s)]|$)", versions["stdout"]):
            raise RuntimeError("This submission is pinned to Lean 4.19.0")
        run("02_lake_version", ["lake", "--version"])
        for dependency in manifest["packages"]:
            folder = ROOT / manifest["packagesDir"] / dependency["name"]
            if not folder.is_dir():
                raise RuntimeError(f"Missing dependency {dependency['name']}; first prepare the pinned dependencies as explained in README.md")
            actual = subprocess.run(["git", "-C", str(folder), "rev-parse", "HEAD"],
                                    text=True, capture_output=True, timeout=30, check=False)
            if actual.returncode or actual.stdout.strip() != dependency["rev"]:
                raise RuntimeError(f"Dependency HEAD mismatch: {dependency['name']}")
            dirty = subprocess.run(["git", "-C", str(folder), "status", "--porcelain", "--untracked-files=no"],
                                   text=True, capture_output=True, timeout=30, check=False)
            if dirty.returncode or dirty.stdout.strip():
                raise RuntimeError(f"Tracked dependency files are modified: {dependency['name']}")
            report["dependencies"].append({"name": dependency["name"],
                                           "commit": actual.stdout.strip(), "tracked_source_clean": True})
        save()
        if args.also_lake_build:
            run("03_lake_build", ["lake", "build", "JSP301"])
        run("04_smoke_test", ["lake", "env", "lean", "tests/SmokeTest.lean"])
        # Never use an existing .olean as evidence that the submitted file checks.
        olean = log_dir / "JSP301.olean"
        if olean.exists():
            olean.unlink()
        proof = run("05_source_compilation", ["lake", "env", "lean", "-o", str(olean), "JSP301.lean"])
        if not olean.is_file() or not olean.stat().st_size:
            raise RuntimeError("Successful exit but no newly generated proof artifact")
        for name in THEOREMS:
            match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", proof["stdout"])
            if not match:
                raise RuntimeError(f"Axiom audit output missing for {name}")
            axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
            if axioms != EXPECTED_AXIOMS:
                raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms)}")
            report["axiom_audit"][name] = sorted(axioms)
        negative = run("06_negative_control", ["lake", "env", "lean", "tests/NegativeControl.lean"], 1)
        if "unsolved goals" not in negative["stdout"] or "False" not in negative["stdout"]:
            raise RuntimeError("Negative control failed for an unexpected reason")
        report["generated_olean"] = {"bytes": olean.stat().st_size,
                                      "sha256": hashlib.sha256(olean.read_bytes()).hexdigest()}
        report["all_passed"] = True
        print("PASS: source compiled; expected axiom sets; false control rejected.")
        return 0
    except Exception as exc:
        report["error"] = f"{type(exc).__name__}: {exc}"
        print(report["error"], file=sys.stderr)
        return 1
    finally:
        report["completed_utc"] = utc()
        save()


if __name__ == "__main__":
    raise SystemExit(main())
