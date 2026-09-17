"""Reproduce local proof checks; run after fetching the pinned Lean dependencies."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
EXPECTED_MATHLIB = "5ed2965256430c3649e86755f9576b54eca72435"


def main():
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["PYTHONIOENCODING"] = "utf-8"
    commands = [
        ["lake", "env", "lean", "--version"],
        ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
        ["lake", "build", "WangExamples", "Inheritance", "Audit"],
        ["lake", "env", "lean", "-j1", "-M4096", "WangExamples.lean"],
        ["lake", "env", "lean", "-j1", "-M4096", "Inheritance.lean"],
        ["lake", "env", "lean", "-j1", "-M4096", "Audit.lean"],
        ["lake", "env", "leanchecker", "WangExamples", "Inheritance", "Audit"],
        [sys.executable, "check_arithmetic.py"],
    ]
    log = []
    for index, command in enumerate(commands):
        display = ["python", *command[1:]] if command[0] == sys.executable else command
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                text=True, encoding="utf-8", errors="replace")
        output = (result.stdout + result.stderr).replace(str(ROOT), "<package>")
        section = f"$ {' '.join(display)}\n{output.rstrip()}\nexit_code={result.returncode}\n"
        print(section, flush=True)
        log.append(section)
        (ROOT / "verification-local.txt").write_text("\n".join(log), encoding="utf-8")
        if result.returncode:
            raise SystemExit(result.returncode)
        if index == 0 and "version 4.34.0," not in output:
            raise SystemExit("Unexpected Lean version")
        if index == 1 and result.stdout.strip() != EXPECTED_MATHLIB:
            raise SystemExit("Unexpected Mathlib revision")
        if index in (3, 4, 5) and ("sorryAx" in output or "Lean.ofReduceBool" in output):
            raise SystemExit("Unexpected trusted dependency in axiom audit")
    print("All local checks passed. Designated independent review remains pending.")


if __name__ == "__main__":
    main()
