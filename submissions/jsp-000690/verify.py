#!/usr/bin/env python3
"""Rebuild in a fresh directory and replay Main with the bundled Lean kernel.

No network access or third-party Python packages are needed. This is local
reproducibility evidence, not an independent implementation of Lean's kernel.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
EXPECTED_COMMIT = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"
EXPECTED_AXIOMS = {
    "jsp_000690": {"propext", "Quot.sound"},
    "no_fewer_colors": {"propext", "Quot.sound"},
    "proper_subgraph_colorable": {"propext"},
    "proper_iff_nonmonochromatic": {"propext", "Classical.choice", "Quot.sound"},
    "vertex_deletion_restricted": {"propext"},
    "deletion_chromatic_number_two": {"propext", "Quot.sound"},
}


def run(argv, *, cwd, env):
    completed = subprocess.run(argv, cwd=cwd, env=env, text=True,
                               encoding="utf-8", errors="strict",
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=300)
    # The commands and output contain no local absolute paths on success.
    print(completed.stdout, end="", flush=True)
    if completed.returncode:
        raise SystemExit(completed.returncode)
    return completed.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.34.0 executable")
    parser.add_argument("--leanchecker", default="leanchecker",
                        help="Lean 4.34.0 bundled checker executable")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    checker = shutil.which(args.leanchecker)
    if not lean or not checker:
        raise SystemExit("Install the pinned Lean toolchain or pass both executable paths.")
    env = os.environ.copy()
    with tempfile.TemporaryDirectory(prefix="jsp690-") as tmp:
        # The only project module available is a fresh copy of this source.
        env["LEAN_PATH"] = tmp
        shutil.copyfile(ROOT / "Main.lean", Path(tmp) / "Main.lean")
        version = run([lean, "--version"], cwd=tmp, env=env)
        if "version 4.34.0," not in version or EXPECTED_COMMIT not in version:
            raise SystemExit("Unexpected Lean version/commit.")
        source = (ROOT / "Main.lean").read_bytes()
        print("Main.lean SHA-256:", hashlib.sha256(source).hexdigest(), flush=True)
        print("Compile and audit:", flush=True)
        output = run([lean, "-o", "Main.olean", "Main.lean"], cwd=tmp, env=env)
        if "warning:" in output or "error:" in output:
            raise SystemExit("Unexpected compiler diagnostics.")
        matches = re.findall(r"'JSP690\.([^']+)' depends on axioms: \[([^\]]*)\]", output)
        found = {name: set(filter(None, (x.strip() for x in axioms.split(","))))
                 for name, axioms in matches}
        if found != EXPECTED_AXIOMS:
            raise SystemExit("Axiom audit differs from the expected theorem list and dependencies.")
        print("Replay Main declarations using the bundled kernel:", flush=True)
        run([checker, "-v", "Main"], cwd=tmp, env=env)
        print("PASS: fresh compilation, six axiom reports, and bundled-kernel replay.", flush=True)


if __name__ == "__main__":
    main()
