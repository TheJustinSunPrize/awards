#!/usr/bin/env python3
"""Reproduce the local checks. Run after fetching the pinned Lake dependencies."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROOF_FILES = ("SunPrize621/Finite.lean", "SunPrize621.lean")
REQUIRED_AUDITS = {
    "SunPrize621.base_local_certificate",
    "SunPrize621.nine_contains_progression",
    "SunPrize621.realBase_almostSidon",
    "SunPrize621.realBase_has_eight",
    "SunPrize621.admissible_le_four_sevenths",
}


def execute(args):
    started = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = (proc.stdout + proc.stderr).replace(str(ROOT), "$PROJECT")
    return {"command": args, "exit_code": proc.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3), "output": output}


def axiom_records(text):
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    return {name: {a.strip() for a in axioms.split(",") if a.strip()}
            for name, axioms in matches}


def permitted(records):
    return bool(records) and all(a <= ALLOWED_AXIOMS for a in records.values())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-replay", action="store_true",
                        help="Skip fresh-kernel replay; the receipt records this omission.")
    args = parser.parse_args()
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    result = {"checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "award_confirmed": False, "organizer_verification": "pending"}
    forbidden = r"\b(sorry|admit|axiom|native_decide|unsafe|run_tac|run_elab|initialize)\b"
    for name in PROOF_FILES:
        assert not re.search(forbidden, (ROOT / name).read_text()), name
    result["proof_source_policy"] = "pass"

    version = execute(["lake", "env", "lean", "--version"])
    assert version["exit_code"] == 0 and "version 4.34.0," in version["output"], version
    result["toolchain"] = version
    build = execute(["lake", "build"])
    assert build["exit_code"] == 0, build
    result["build"] = build
    audit = execute(["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"])
    assert audit["exit_code"] == 0, audit
    records = axiom_records(audit["output"])
    assert REQUIRED_AUDITS <= records.keys() and permitted(records), audit
    result["axiom_audit"] = audit
    result["axiom_dependencies"] = {n: sorted(v) for n, v in records.items()}

    with tempfile.TemporaryDirectory(prefix="verification-negative-", dir=ROOT) as tmp:
        tmp = Path(tmp)
        cases = {
            "false_arithmetic": "example : (1 : Nat) = 2 := by decide +kernel\n",
            "placeholder": "theorem incomplete : False := by sorry\n",
            "custom_axiom": "axiom unexpected_axiom : False\n"
                            "theorem contaminated : False := unexpected_axiom\n"
                            "#print axioms contaminated\n",
        }
        outcomes = {}
        for name, source in cases.items():
            file = tmp / (name + ".lean")
            file.write_text(source)
            run = execute(["lake", "env", "lean", "-DwarningAsError=true",
                           str(file.relative_to(ROOT))])
            if name == "custom_axiom":
                dependencies = axiom_records(run["output"])
                assert run["exit_code"] == 0 and dependencies and not permitted(dependencies), run
                outcomes[name] = "rejected by the axiom allowlist"
            else:
                assert run["exit_code"] != 0, run
                outcomes[name] = "rejected by Lean with warnings as errors"
        result["negative_controls"] = outcomes

    if args.skip_replay:
        result["fresh_kernel_replay"] = "not run in this invocation"
    else:
        replay = execute(["lake", "env", "leanchecker", "--verbose", "--fresh", "SunPrize621"])
        assert replay["exit_code"] == 0, replay
        result["fresh_kernel_replay"] = replay
    result["checker_limitation"] = (
        "leanchecker uses the bundled Lean kernel, not an independently implemented checker; "
        "upstream cached library artifacts were used, not a full source rebuild of all imports."
    )
    result["source_files"] = {}
    for name in (*PROOF_FILES, "Audit.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        data = (ROOT / name).read_bytes()
        result["source_files"][name] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    result["local_validation"] = "pass"
    (evidence / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    (evidence / "axioms.txt").write_text(audit["output"])
    print("Local validation passed; organizer verification and award review remain pending.")


if __name__ == "__main__":
    main()
