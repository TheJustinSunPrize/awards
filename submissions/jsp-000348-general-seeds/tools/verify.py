"""Build, audit every named theorem, check definitions, and replay the official kernel."""
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
    source = (ROOT / "GeneralSeeds.lean").read_text()
    if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source):
        raise RuntimeError("Unexpected trusted escape or unfinished declaration")
    declarations = re.findall(r"^theorem ([\w_]+)", source, re.M)
    audit_source = (ROOT / "Audit.lean").read_text()
    if any(f"#print axioms GeneralSeeds.{name}\n" not in audit_source for name in declarations):
        raise RuntimeError("An exported theorem is missing from the audit")
    steps = {}
    steps["environment"], _ = run("environment", ["python3", "tools/check_environment.py"])
    steps["build"], build = run("build", ["lake", "build"])
    if re.search(r"\b(?:error|warning):", build):
        raise RuntimeError("Build emitted warnings or errors")
    steps["axioms"], audit = run("axioms", ["lake", "env", "lean", "Audit.lean"])
    reports = re.findall(r"'GeneralSeeds\.([\w_]+)' depends on axioms: \[([^]]*)\]", audit)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if {name for name, _ in reports} != set(declarations):
        raise RuntimeError("Incomplete axiom audit")
    for name, axioms in reports:
        if not set(filter(None, axioms.split(", "))).issubset(allowed):
            raise RuntimeError(f"Unexpected axiom closure: {name}")
    steps["small_cases"], _ = run("small-cases", ["python3", "tools/check_small.py"])
    steps["kernel_replay"], _ = run("kernel-replay",
        ["lake", "env", "leanchecker", "--fresh", "--verbose", "GeneralSeeds"])
    inputs = {}
    for name in ["GeneralSeeds.lean", "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
        data = (ROOT / name).read_bytes()
        inputs[name] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    logs = {}
    for path in sorted(OUT.glob("*.log")):
        data = path.read_bytes()
        logs[path.name] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    (OUT / "verification.json").write_text(json.dumps({
        "steps": steps, "theorem_count": len(declarations), "inputs": inputs, "logs": logs,
        "limits": ["Compiled dependency caches used; not all dependencies rebuilt from source.",
                   "Fresh replay uses Lean's official kernel, not an independent implementation.",
                   "Finite examples do not establish the infinite conclusions.",
                   "No organizer-designated verification or award acceptance is claimed."]
    }, indent=2) + "\n")
    print(json.dumps(steps, indent=2))


if __name__ == "__main__":
    main()
