#!/usr/bin/env python3
"""Build and replay the Bourque-Ligh proof with the pinned Lean toolchain."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "verification" / "local"
LOGS.mkdir(parents=True, exist_ok=True)


def run(name, command):
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (LOGS / name).write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


run("toolchain.log", ["lake", "env", "lean", "--version"])
run("build.log", ["lake", "build"])
output = run("replay.log", ["lake", "env", "lean", "BourqueLigh.lean"])
audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
expected = {
    "BourqueLigh.not_conjecture",
    "BourqueLigh.not_realConjecture",
    "BourqueLigh.exists_gcdClosed_singular_lcmMatrix",
}
if len(audits) != len(expected) or {name for name, _ in audits} != expected:
    sys.exit("Expected exactly one axiom audit for each of the three final theorems.")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, audit in audits:
    actual = {item.strip() for item in audit.split(",") if item.strip()}
    if not actual <= allowed:
        sys.exit(f"Unexpected axiom dependencies: {actual - allowed}")
if "sorryAx" in output or "declaration uses 'sorry'" in output:
    sys.exit("An admitted proof was reported.")
print(f"Verified build, source replay and {len(audits)} axiom audits.")
