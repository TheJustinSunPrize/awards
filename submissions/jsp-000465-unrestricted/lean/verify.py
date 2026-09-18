"""Compile the proof and reject unexpected axioms in its final theorem."""

import re
import subprocess
from pathlib import Path


def main():
    result = subprocess.run(
        ["lake", "env", "lean", "Erdos575.lean"],
        cwd=Path(__file__).resolve().parent,
        text=True,
        encoding="utf-8",
        capture_output=True,
        check=False,
    )
    print(result.stdout, end="")
    print(result.stderr, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    match = re.search(
        r"'Erdos575\.not_unrestrictedCompactness' depends on axioms:\s*\[([^\]]*)\]",
        result.stdout,
    )
    if not match:
        raise SystemExit("Missing final theorem axiom audit")
    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected axioms: {sorted(axioms - allowed)}")
    print("PASS: compilation and transitive axiom audit")


if __name__ == "__main__":
    main()
