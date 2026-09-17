#!/usr/bin/env python3
"""Recheck an exported proof and true/false controls using an existing Nanoda binary.

No downloading, compilation, or publication occurs. Run under an OS network
sandbox when isolation is required; this script does not claim to create one.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


AXIOMS = ["Classical.choice", "Quot.sound", "propext"]


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--kit", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--results", type=Path, default=Path("offline-results"))
    args = parser.parse_args()
    kit, results, checker = args.kit.resolve(), args.results.resolve(), args.checker.resolve()
    results.mkdir(parents=True, exist_ok=True)
    report = {"started_utc": datetime.now(timezone.utc).isoformat(), "status": "running",
              "checks": [], "network_isolation": "Must be supplied and evidenced by the caller",
              "trust_boundary": "Submitter-run checking is not organizer verification or an award decision."}
    try:
        manifest = json.loads((kit / "MANIFEST.json").read_text())
        if manifest["permitted_axioms"] != AXIOMS:
            raise RuntimeError("Unexpected axiom policy")
        for item in manifest["files"]:
            path = (kit / item["path"]).resolve()
            if not path.is_relative_to(kit) or not path.is_file():
                raise RuntimeError("Manifest path is outside the kit or not a file")
            if path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
                raise RuntimeError("Manifest mismatch: " + item["path"])
        report["manifest_sha256"] = digest(kit / "MANIFEST.json")
        report["checker_sha256"] = digest(checker)
        report["proof_source_commit"] = manifest["proof_source_commit"]
        report["toolchain"] = manifest["toolchain"]
        expected = manifest["expected_checked_declarations"]
        for name, filename, negative in [
            ("proof", "proofs.ndjson", False),
            ("positive-control", "positive-control.ndjson", False),
            ("negative-control", "negative-control.ndjson", True),
        ]:
            # Nanoda opens this destination without the create flag.
            printer = results / (name + "-axioms.txt")
            printer.write_text("")
            config = {"export_file_path": str(kit / filename), "use_stdin": False,
                      "permitted_axioms": AXIOMS, "unpermitted_axiom_hard_error": True,
                      "unsafe_permit_all_axioms": False, "num_threads": 2,
                      "nat_extension": True, "string_extension": True,
                      "pp_output_path": str(printer),
                      "print_success_message": True}
            config_path = results / (name + ".json")
            config_path.write_text(json.dumps(config, indent=2) + "\n")
            proc = subprocess.run([str(checker), str(config_path)], cwd=kit,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  text=True, timeout=600)
            output = proc.stdout.replace(str(kit), "<KIT>").replace(str(results), "<RESULTS>")
            output = output.replace(str(checker), "<NANODA>")
            log = results / (name + ".log")
            log.write_text(output)
            count = re.search(r"Checked (\d+) declarations with no errors", output)
            report["checks"].append({"name": name, "exit_code": proc.returncode,
                                      "expected_failure": negative, "log": log.name,
                                      "log_sha256": digest(log),
                                      "checked_declarations": int(count[1]) if count else None})
            print(f"{name}: exit {proc.returncode}", flush=True)
            if negative:
                if proc.returncode == 0 or "self.def_eq(u, v)" not in output:
                    raise RuntimeError("False-type control was not rejected by the proof checker")
            elif proc.returncode or not count or (name == "proof" and int(count[1]) != expected):
                raise RuntimeError("Proof check failed or returned an unexpected declaration count")
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        message = str(exc).replace(str(kit), "<KIT>").replace(str(results), "<RESULTS>")
        report["error"] = message.replace(str(checker), "<NANODA>")
        print(report["error"], file=sys.stderr)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (results / "offline-report.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
