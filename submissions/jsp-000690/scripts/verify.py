#!/usr/bin/env python3
"""Build the pinned project, check theorem axioms, and record source hashes.

Uses only Python's standard library. The checker does not supply mathematical
assumptions to Lean. A new directory or --clean gives a build from source.
"""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_VERSION = "4.34.0"
EXPECTED_COMMIT = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
EXPECTED_THEOREMS = {
    "JSP690.not_bool_colorable",
    "JSP690.not_colorable_of_lt_three",
    "JSP690.edgeDeletionColor_proper",
    "JSP690.vertexDeletionColor_proper",
    "JSP690.edge_eq_iff_vertices",
    "JSP690.strictSubgraphOn_colorable_of_deletions",
    "JSP690.witness_chromatic_critical",
    "JSP690.jsp_000690_nine_vertices",
    "JSP690.jsp_000690",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Path to Lake; defaults to PATH")
    parser.add_argument("--clean", action="store_true", help="Remove this package's build cache first")
    args = parser.parse_args()
    lake = args.lake or shutil.which("lake")
    if not lake:
        parser.error("Lake not found. Install the pinned Lean toolchain or pass --lake.")
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    log_path = out / "build-and-axioms.log"
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as log:
        def run(arguments):
            # Normalize only the executable path in public logs.
            public_command = " ".join(["lake"] + arguments[1:])
            print("Running:", public_command, flush=True)
            log.write("$ " + public_command + "\n")
            log.flush()
            result = subprocess.run(arguments, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, check=False)
            print(result.stdout, end="", flush=True)
            log.write(result.stdout)
            log.flush()
            if result.returncode:
                raise RuntimeError("Command failed with exit code " + str(result.returncode))
            return result.stdout

        version = run([lake, "env", "lean", "--version"])
        if "version " + EXPECTED_VERSION + "," not in version or EXPECTED_COMMIT not in version:
            raise RuntimeError("Unexpected Lean version or commit; use lean-toolchain.")
        if args.clean:
            run([lake, "clean"])
        run([lake, "build"])
        audit = run([lake, "env", "lean", "Audit.lean"])
        axioms = {}
        for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
            axioms[name] = [item.strip() for item in raw.split(",") if item.strip()]
        for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
            axioms[name] = []
        if set(axioms) != EXPECTED_THEOREMS:
            raise RuntimeError("Missing or unexpected axiom audit entries: " + repr(set(axioms)))
        for name, dependencies in axioms.items():
            bad = set(dependencies) - ALLOWED_AXIOMS
            if bad:
                raise RuntimeError("Unapproved axiom dependency in " + name + ": " + repr(bad))
        paths = sorted((ROOT / "JSP690").glob("*.lean"))
        paths += [ROOT / name for name in
                  ("JSP690.lean", "Audit.lean", "lean-toolchain", "lakefile.toml",
                   "lake-manifest.json", "scripts/verify.py")]
        hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in paths}
        report = {
            "status": "passed",
            "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "lean_version": EXPECTED_VERSION,
            "lean_commit": EXPECTED_COMMIT,
            "clean_requested": args.clean,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "axioms": axioms,
            "source_sha256": hashes,
        }
        (out / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("PASS: build and all nine theorem axiom audits succeeded.", flush=True)
        log.write("PASS: build and all nine theorem axiom audits succeeded.\n")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError) as error:
        print("FAILED:", error, file=sys.stderr)
        sys.exit(1)
