#!/usr/bin/env python3
"""Verify the bridge in a dedicated, pinned Mathlib checkout.

This downloads two hash-pinned public dependencies; it does not redistribute them.
Use a fresh checkout: source paths already holding different bytes are rejected.
"""
import argparse, hashlib, json, re, subprocess, sys, urllib.request
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write_exact(path, data):
    if path.exists() and path.read_bytes() != data:
        raise RuntimeError(f"Existing file differs; use a fresh checkout: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--mathlib", type=Path, required=True,
                   help="Dedicated Mathlib checkout, with its cache already installed")
    a = p.parse_args()
    work = a.mathlib.resolve()
    refs = json.loads((HERE / "upstream.json").read_text(encoding="utf8"))
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()
    if head != refs["mathlib_commit"]:
        raise RuntimeError("Mathlib checkout does not match the recorded commit")
    toolchain = (work / "lean-toolchain").read_text().strip()
    if toolchain != refs["lean_toolchain"]:
        raise RuntimeError("Lean toolchain does not match the recorded version")
    version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=work, text=True).strip()
    if not re.search(r"\bversion\s+4\.33\.0(?:[,\s])", version):
        raise RuntimeError("Actual Lean executable is not the pinned 4.33.0 release: " + version)
    modules = []
    sources = []
    for row in refs["files"]:
        rel = Path(row["module"].replace(".", "/") + ".lean")
        target = work / rel
        if target.exists() and sha(target.read_bytes()) == row["sha256"]:
            data = target.read_bytes()
        else:
            with urllib.request.urlopen(row["url"], timeout=60) as response:
                data = response.read()
        if sha(data) != row["sha256"]:
            raise RuntimeError(f"Upstream hash mismatch: {row['module']}")
        write_exact(target, data)
        modules.append(row["module"])
        sources.append({"module":row["module"],"sha256":sha(data)})
    bridge = (HERE / "JSP410ClosedBridge.lean").read_bytes()
    expected = json.loads((HERE / "verification.json").read_text(encoding="utf8"))
    if sha(bridge) != expected["bridge_sha256"]:
        raise RuntimeError("Bridge source bytes differ from the published verification record")
    write_exact(work / "JSP410ClosedBridge.lean", bridge)
    modules.append("JSP410ClosedBridge")
    sources.append({"module":"JSP410ClosedBridge","sha256":sha(bridge)})
    logs = HERE / "verification" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    logs.mkdir(parents=True, exist_ok=False)
    result = {"lean_version":version,"mathlib_commit":head,"sources":sources,"events":[],
              "scope":"Compiled custom sources; target-module Lean kernel replay against imported Mathlib cache."}
    commands = []
    for module in modules:
        rel = module.replace(".", "/")
        output = Path(".lake/build/lib/lean") / (rel + ".olean")
        (work / output).parent.mkdir(parents=True, exist_ok=True)
        commands.append((module,"compile",["lake","env","lean","-j1","-M8192",
                                         "-o",str(output),rel+".lean"]))
    commands.append(("JSP410ClosedBridge","replay",
                     ["lake","env","leanchecker","--verbose","JSP410ClosedBridge"]))
    for module,stage,cmd in commands:
        log = logs / (module + "." + stage + ".log")
        print(stage, module, flush=True)
        with log.open("wb") as f:
            run = subprocess.run(cmd,cwd=work,stdout=f,stderr=subprocess.STDOUT)
        result["events"].append({"module":module,"stage":stage,"command":cmd,
                                 "exit_code":run.returncode,"log":log.name,
                                 "log_sha256":sha(log.read_bytes())})
        (logs/"result.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
        if run.returncode:
            raise RuntimeError(f"{stage} failed for {module}; see {log}")
        if module == "JSP410ClosedBridge" and stage == "compile":
            output = log.read_text(encoding="utf8", errors="replace")
            reports = {}
            for theorem in expected["theorems"]:
                matches = re.findall(re.escape("'" + theorem["name"] + "'") +
                                     r" depends on axioms:\s*\[([^]]*)\]", output)
                if not matches:
                    raise RuntimeError("Missing axiom report: " + theorem["name"])
                axioms = [x.strip() for x in matches[-1].split(",") if x.strip()]
                if not set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}:
                    raise RuntimeError("Unexpected target theorem axioms: " + repr(axioms))
                reports[theorem["name"]] = axioms
            result["target_axioms"] = reports
            (logs/"result.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print("All custom modules compiled; target replay exited 0.")
    print("Read the bridge compile log for the actual theorem-axiom report.")

if __name__ == "__main__":
    main()
