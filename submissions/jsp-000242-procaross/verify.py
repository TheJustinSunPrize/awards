#!/usr/bin/env python3
"""Compile, audit, replay, and reject a false certificate. Does not download or publish."""
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

DECLARATIONS = [
    "recips_le_envelope", "possible_of_rep", "rep_of_possible", "possible_of_finset",
    "certificate_seven", "possible_iff_finset", "exact_three", "exact_four", "exact_five",
    "exact_six", "exact_seven", "exact_eight", "exact_nine", "exact_ten", "exact_eleven",
    "exact_twelve",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--mathlib", type=Path, help="Existing pinned Mathlib checkout; optional")
    parser.add_argument("--package-overrides", type=Path, help="Lake archive/path overrides; optional")
    parser.add_argument("--results", type=Path, default=Path("verification/latest"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    mathlib = (args.mathlib or root / ".lake/packages/mathlib").resolve()
    environment = mathlib if args.mathlib else root
    results = args.results.resolve()
    results.mkdir(parents=True, exist_ok=True)
    build = results / "build"
    build.mkdir(exist_ok=True)
    pins = json.loads((root / "source-pins.json").read_text())
    env = os.environ.copy()
    if args.lean_bin:
        env["PATH"] = str(args.lean_bin.resolve()) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    executables = {name: shutil.which(name, path=env.get("PATH"))
                   for name in ["lake", "lean", "leanchecker"]}
    if not all(executables.values()):
        parser.error("lake, lean, and leanchecker must be available (or supply --lean-bin)")
    report = {"started_utc": datetime.now(timezone.utc).isoformat(), "status": "running",
              "checks": [], "axioms": {}, "trust_boundary": [
                  "The bundled leanchecker reuses Lean's kernel; it is not an independent verifier.",
                  "Imported Lean and Mathlib declarations are trusted, not replayed from scratch.",
                  "Compilation and replay do not establish mathematical novelty or prize eligibility.",
              ]}

    def redact(text: str) -> str:
        # Public logs deliberately omit machine-specific filesystem paths.
        replacements = [(root, "<PACKAGE>"), (results, "<RESULTS>"),
                        (mathlib, "<MATHLIB>"), (environment, "<ENVIRONMENT>")]
        if args.lean_bin:
            replacements.append((args.lean_bin.resolve(), "<LEAN_BIN>"))
        if args.package_overrides:
            replacements.append((args.package_overrides.resolve(), "<PACKAGE_OVERRIDES>"))
        replacements.sort(key=lambda row: len(str(row[0])), reverse=True)
        for path, replacement in replacements:
            text = text.replace(str(path), replacement)
        return text

    def run(name: str, command: list[str], cwd: Path = root, expected_failure=False) -> str:
        proc = subprocess.run(command, cwd=cwd, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        text = redact(proc.stdout)
        log = results / f"{name}.log"
        log.write_text(text)
        report["checks"].append({"name": name, "command": [Path(command[0]).name] +
                                  [redact(x) for x in command[1:]],
                                  "exit_code": proc.returncode, "expected_failure": expected_failure,
                                  "log": log.name, "log_sha256": digest(log)})
        print(f"{name}: exit {proc.returncode}", flush=True)
        if expected_failure:
            if proc.returncode == 0 or "error:" not in text or "decide" not in text:
                raise RuntimeError("The intentionally false certificate was not rejected as expected")
        elif proc.returncode:
            raise RuntimeError(f"{name} failed; see {log.name}")
        return proc.stdout

    try:
        for name, sha in pins["mathlib_configuration_sha256"].items():
            if digest(mathlib / name) != sha:
                raise RuntimeError(f"Pinned Mathlib configuration differs: {name}")
        for name, sha in pins["proof_sha256"].items():
            if digest(root / name) != sha:
                raise RuntimeError(f"Source hash differs: {name}")
        version = run("lean-version", [executables["lean"], "--version"])
        if "version 4.34.0," not in version or pins["lean_commit"] not in version:
            raise RuntimeError("Unexpected Lean version or commit")
        lake = [executables["lake"]]
        if args.package_overrides:
            lake.append("--packages=" + str(args.package_overrides.resolve()))
        path_proc = subprocess.run(lake + ["env", "printenv", "LEAN_PATH"],
                                   cwd=environment, env=env, text=True, capture_output=True,
                                   timeout=60, check=True)
        paths = [str((environment / path).resolve()) if not Path(path).is_absolute() else path
                 for path in path_proc.stdout.strip().split(os.pathsep) if path]
        env["LEAN_PATH"] = os.pathsep.join([str(build)] + paths)
        text = run("compile", [executables["lean"], "-DautoImplicit=false", "-DwarningAsError=true",
                               "-o", str(build / "UnitFractionBounds.olean"), "UnitFractionBounds.lean"])
        audits = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text))
        for short in DECLARATIONS:
            name = "UnitFractionBounds." + short
            if name not in audits:
                raise RuntimeError(f"Missing axiom report: {name}")
            axioms = {x.strip() for x in audits[name].split(",") if x.strip()}
            if not axioms <= ALLOWED:
                raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms)}")
            report["axioms"][name] = sorted(axioms)
        run("replay", [executables["leanchecker"], "--verbose", "UnitFractionBounds"])
        positive = build / "PositiveCertificate.lean"
        positive.write_text("import UnitFractionBounds\n"
                            "example : UnitFractionBounds.possible 3 2 1 = true := by decide +kernel\n"
                            "example : UnitFractionBounds.possible 7 4 1 = false := by decide +kernel\n")
        run("positive-certificate", [executables["lean"], positive.name], cwd=build)
        control = build / "FalseCertificate.lean"
        control.write_text("import UnitFractionBounds\n"
                           "example : UnitFractionBounds.possible 3 2 1 = false := by decide +kernel\n")
        run("false-certificate", [executables["lean"], control.name],
            cwd=build, expected_failure=True)
        report["source_sha256"] = {"UnitFractionBounds.lean": digest(root / "UnitFractionBounds.lean"),
                                     "verify.py": digest(root / "verify.py")}
        report["object_sha256"] = digest(build / "UnitFractionBounds.olean")
        report["mathlib_revision"] = pins["mathlib_revision"]
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = redact(str(exc))
        print(report["error"], file=sys.stderr)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (results / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
