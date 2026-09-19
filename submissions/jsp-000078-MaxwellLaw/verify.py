#!/usr/bin/env python3
"""Reproduce source identity checks, Lean build, axiom audit, and module replay."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import time

root = Path(__file__).resolve().parent
os.chdir(root)
logs = root / "logs"
logs.mkdir(exist_ok=True)
env = dict(os.environ)
env.setdefault("LEAN_NUM_THREADS", "2")
records = []

def run(name, args):
    print(f"Running {name}: {' '.join(args)}", flush=True)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    before = time.monotonic()
    log_path = logs / f"{name}.log"
    with log_path.open("w") as output_file:
        result = subprocess.run(args, text=True, stdout=output_file,
                                stderr=subprocess.STDOUT, env=env)
    output = log_path.read_text()
    records.append({"stage": name, "command": args, "started_utc": started,
                    "duration_seconds": round(time.monotonic() - before, 3),
                    "exit_code": result.returncode})
    (logs / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
    if result.returncode:
        print(output[-10000:])
        raise SystemExit(f"{name} failed; see logs/{name}.log")
    return output

run("sources", ["python3", "verify_sources.py"])
version = run("toolchain", ["lake", "env", "lean", "--version"]).strip()
run("build", ["lake", "build"])
audit = run("axioms", ["lake", "env", "lean", "Audit.lean"])
expected = {
    "Jsp000078.colorable_of_finite_induced",
    "Jsp000078.oddCycleLengths_eq",
    "Erdos58.erdos_58",
    "Jsp000078.erdos_58_encard",
    "Jsp000078.erdos_58",
}
found = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit))
if set(found) != expected:
    raise SystemExit(f"Unexpected axiom report names: {set(found)}")
axioms = {name: sorted(filter(None, (x.strip() for x in values.split(","))))
          for name, values in found.items()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, values in axioms.items():
    if not set(values) <= allowed:
        raise SystemExit(f"Disallowed axiom dependency for {name}: {values}")
manifest = json.loads((root / "vendor-manifest.json").read_text())
modules = [x["path"].removesuffix(".lean").replace("/", ".")
           for x in manifest["files"]]
modules += ["Jsp000078.CycleLengths", "Jsp000078.Compactness",
            "Jsp000078.General", "Jsp000078"]
replay = run("replay", ["lake", "env", "lean", "--run", "ReplayBatch.lean", *modules])
collected = re.findall(r"^Collected (.+)$", replay, re.MULTILINE)
result = re.search(r"Successfully replayed (\d+) declarations from (\d+) modules\.", replay)
if collected != modules or result is None or int(result[2]) != len(modules):
    raise SystemExit("Incomplete kernel replay coverage report")
sources = sorted(
    [p for p in root.rglob("*.lean") if ".lake" not in p.parts and "logs" not in p.parts]
    + [root / "lakefile.toml", root / "lake-manifest.json", root / "lean-toolchain"]
)
hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sources}
summary = {
    "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "platform": f"{platform.system()} {platform.release()} {platform.machine()}",
    "lean": version,
    "replayed_module_count": len(modules),
    "replayed_declaration_count": int(result[1]),
    "axioms": axioms,
    "commands": records,
    "source_sha256": hashes,
    "scope": "Custom modules compiled from source; all custom declarations replayed into a Mathlib-only environment using the same Lean kernel; "
             "official dependency caches used; not a full fresh replay of Mathlib "
             "or an independently implemented verifier."
}
(logs / "verification-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({k: summary[k] for k in
                 ["completed_utc", "lean", "replayed_module_count", "replayed_declaration_count", "axioms"]}, indent=2))
