#!/usr/bin/env python3
"""Compile the proof, audit final axioms, and replay its declarations."""
from pathlib import Path
import subprocess, re, json, time
root = Path(__file__).resolve().parent
checks = []
for cmd in (["lake", "build", "Proof"], ["lake", "env", "lean", "-j1", "Proof.lean"],
            ["lake", "env", "leanchecker", "-v", "Proof"]):
    start = time.monotonic()
    p = subprocess.run(cmd, cwd=root, text=True, capture_output=True)
    print(p.stdout, end="")
    print(p.stderr, end="")
    checks.append({"command": cmd, "exit_code": p.returncode,
                   "seconds": round(time.monotonic()-start, 3)})
    if p.returncode:
        raise SystemExit(p.returncode)
    if cmd[2:3] == ["lean"]:
        audits = dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", p.stdout))
        for name in ("left_minimum", "right_minimum", "minima_values", "refutation"):
            ax = {x.strip() for x in audits["LinWimmer."+name].split(",") if x.strip()}
            if ax != {"propext", "Classical.choice", "Quot.sound"}:
                raise SystemExit(f"Unexpected axiom footprint for {name}: {ax}")
print(json.dumps({"checks": checks, "note": "Same-kernel replay, not an independent kernel or organizer review."}, indent=2))
