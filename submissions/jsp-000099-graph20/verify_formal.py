"""Reproduce this local proof package using an already prepared Lean/Mathlib setup.

Uses Lean's official fresh kernel replay, not an independent proof-checker engine.
No dependency downloads or external publication are performed by this script.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def sources():
    files = list(ROOT.glob("*.lean")) + list(ROOT.glob("*.py"))
    files += [ROOT / n for n in ("witness20.g6", "lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {p.name: sha(p) for p in sorted(files)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-bin", required=True, type=Path)
    args = parser.parse_args()
    binary_dir = args.lean_bin.resolve()
    env = os.environ.copy()
    env["PATH"] = str(binary_dir) + os.pathsep + env.get("PATH", "")
    logs = ROOT / "verification"
    logs.mkdir(exist_ok=True)
    result = {
        "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "meaning": "Local formal verification; not official prize review; not a globally first result",
        "independent_formal_checker": "Not run; leanchecker uses the Lean kernel",
        "source_sha256": sources(),
        "stages": [],
    }

    def run(label, argv, timeout=600):
        start = time.monotonic()
        output = logs / (label + ".log")
        with output.open("w") as stream:
            process = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
        record = {"name": label, "argv": list(map(str, argv)), "exit_code": process.returncode,
                  "seconds": round(time.monotonic() - start, 3), "log": output.name, "log_sha256": sha(output)}
        result["stages"].append(record)
        (logs / "formal-verification.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if process.returncode:
            raise RuntimeError(output.read_text()[-8000:])
        return output.read_text()

    version = run("lean-version", [str(binary_dir / "lean"), "--version"])
    if "version 4.34.0," not in version:
        raise RuntimeError("Expected Lean 4.34.0")
    result["tool_binaries"] = {name: sha(binary_dir / name) for name in ("lean", "lake", "leanchecker")}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    result["dependency_revisions"] = {}
    for dependency in manifest["packages"]:
        directory = ROOT / ".lake/packages" / dependency["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != dependency["rev"]:
            raise RuntimeError("Dependency revision mismatch: " + dependency["name"])
        result["dependency_revisions"][dependency["name"]] = revision

    from generate_certificates import generate
    for d in range(20):
        generated, _ = generate(d)
        if generated.encode() != (ROOT / f"Degree{d}.lean").read_bytes():
            raise RuntimeError(f"Certificate source mismatch for degree {d}")
    result["certificate_regeneration"] = "All 20 modules match byte for byte"

    lake = str(binary_dir / "lake")
    run("build-reproduction", [lake, "build"])
    run("negative-controls", [lake, "env", "lean", "NegativeControls.lean"])
    audit = run("axiom-audit", [lake, "env", "lean", "Audit.lean"])
    declarations = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    if len(declarations) != 2:
        raise RuntimeError("Missing final theorem axiom reports")
    expected = {"propext", "Classical.choice", "Quot.sound"}
    for name, axioms in declarations:
        if {s.strip() for s in axioms.split(",")} != expected:
            raise RuntimeError("Unexpected axioms: " + name)
    result["final_axioms"] = {name: [s.strip() for s in axioms.split(",")] for name, axioms in declarations}

    # An empty target or prefix would check unrelated modules. Specify the exact result module.
    run("fresh-kernel-replay", [lake, "env", "leanchecker", "--fresh", "--verbose", "Graph20Result"])
    if sources() != result["source_sha256"]:
        raise RuntimeError("Proof sources changed during verification")
    result["local_olean_sha256"] = {str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT / ".lake/build/lib/lean").glob("*.olean"))}
    result["completed_at_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result["success"] = True
    (logs / "formal-verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print("All formal verification stages passed.", flush=True)


if __name__ == "__main__":
    main()
