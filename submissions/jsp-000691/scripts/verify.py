"""Build and audit the actual submitted theorem declarations; requires Lake."""
from pathlib import Path
import json
import hashlib
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "Erdos835.property_successor_prime",
    "Erdos835.not_property_of_composite",
}


def run(args, logfile):
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    (EVIDENCE / logfile).write_text(p.stdout)
    if p.returncode:
        raise SystemExit(f"Command failed ({p.returncode}); see evidence/{logfile}")
    return p.stdout


def audit(output):
    found = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        axioms = {s.strip() for s in raw.split(",") if s.strip()}
        if axioms - ALLOWED:
            raise SystemExit(f"Unexpected axioms in {name}: {sorted(axioms - ALLOWED)}")
        found[name] = sorted(axioms)
    if not TARGETS <= found.keys():
        raise SystemExit(f"Missing axiom output: {sorted(TARGETS - found.keys())}")
    return found


def negative_controls():
    controls = {
        "false_arithmetic": "example : (0 : Nat) = 1 := by decide\n",
        "placeholder": (
            "theorem Erdos835.property_successor_prime : False := by sorry\n"
            "#print axioms Erdos835.property_successor_prime\n"
        ),
        "custom_axiom": (
            "axiom unjustified : False\n"
            "theorem Erdos835.property_successor_prime : False := unjustified\n"
            "#print axioms Erdos835.property_successor_prime\n"
        ),
    }
    results = {}
    with tempfile.TemporaryDirectory(prefix="controls-", dir=ROOT / ".lake") as directory:
        for name, source in controls.items():
            path = Path(directory) / f"{name}.lean"
            path.write_text(source)
            p = subprocess.run(["lake", "env", "lean", str(path.relative_to(ROOT))],
                               cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
            output = p.stdout.replace(str(path.relative_to(ROOT)), f"{name}.lean")
            (EVIDENCE / f"{name}.log").write_text(output)
            if name == "false_arithmetic":
                if p.returncode == 0 or "error:" not in output:
                    raise SystemExit("False-arithmetic negative control failed")
                results[name] = "rejected by Lean"
            else:
                if p.returncode:
                    raise SystemExit(f"Control {name} did not reach axiom audit")
                try:
                    audit(output)
                except SystemExit as exc:
                    if "Unexpected axioms" not in str(exc):
                        raise
                    results[name] = "rejected by axiom audit"
                else:
                    raise SystemExit(f"Axiom audit accepted control {name}")
    return results


if __name__ == "__main__":
    EVIDENCE.mkdir(exist_ok=True)
    run(["lake", "build"], "build.log")
    output = run(["lake", "env", "lean", "-DwarningAsError=true", "Prize835.lean"],
                 "axioms.log")
    axioms = audit(output)
    controls = negative_controls()
    source = (ROOT / "Prize835.lean").read_bytes()
    result = {
        "source_file": "Prize835.lean",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "source_bytes": len(source),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": "8f9d9cff6bd728b17a24e163c9402775d9e6a365",
        "axioms": axioms,
        "build": "passed",
        "warnings_as_errors": "passed",
        "negative_controls": controls,
        "independent_checker": "not performed",
        "designated_verification": "pending",
        "award_eligibility": "not established",
    }
    (EVIDENCE / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Build and theorem axiom audit passed.")
