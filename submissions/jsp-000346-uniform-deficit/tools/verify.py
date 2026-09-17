"""Run local proof checks. The pinned compiled Mathlib dependencies are required."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
OUT.mkdir(exist_ok=True)


def run(label, args):
    started = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    elapsed = time.monotonic() - started
    data = proc.stdout + proc.stderr
    (OUT / (label + ".log")).write_text(data)
    if proc.returncode:
        raise RuntimeError(f"{label}: exit {proc.returncode}; see verification/{label}.log")
    return {"command": args, "exit_code": proc.returncode,
            "elapsed_seconds": round(elapsed, 3)}, data


def main():
    steps = {}
    steps["environment"], _ = run("environment", ["python3", "tools/check_environment.py"])
    steps["build"], build = run("build", ["lake", "build"])
    if re.search(r"\b(?:error|warning):", build):
        raise RuntimeError("Build emitted warnings or errors")
    steps["axioms"], audit = run("axioms", ["lake", "env", "lean", "Audit.lean"])
    reports = re.findall(r"depends on axioms: \[([^]]*)\]", audit)
    expected = {"propext", "Classical.choice", "Quot.sound"}
    if len(reports) != 8 or any(set(x.split(", ")) != expected for x in reports):
        raise RuntimeError("Unexpected axiom closure")
    steps["small_cases"], _ = run("small-cases", ["python3", "tools/check_small.py"])
    steps["kernel_replay"], _ = run("kernel-replay",
        ["lake", "env", "leanchecker", "--fresh", "--verbose", "ProductDeficit"])
    inputs = {}
    for name in ["ProductDeficit.lean", "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
        data = (ROOT / name).read_bytes()
        inputs[name] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    logs = {}
    for path in sorted(OUT.glob("*.log")):
        data = path.read_bytes()
        logs[path.name] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    (OUT / "verification.json").write_text(json.dumps({
        "steps": steps, "inputs": inputs, "logs": logs,
        "limits": ["Compiled dependency caches used; not all dependencies rebuilt from source.",
                   "Fresh replay uses Lean's official kernel, not an independent implementation.",
                   "No network or filesystem isolation is claimed.",
                   "No organizer-designated verification or award acceptance is claimed."]
    }, indent=2) + "\n")
    print(json.dumps(steps, indent=2))


if __name__ == "__main__":
    main()
