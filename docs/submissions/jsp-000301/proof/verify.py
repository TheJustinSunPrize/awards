"""Compile the adjacent source with a supplied Lean binary; retain actual evidence."""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean", type=Path, help="Path to the real Lean executable")
    args = parser.parse_args()
    lean = args.lean.resolve(strict=True)
    source = Path(__file__).resolve().with_name("Counterexample.lean")
    evidence = source.parent.parent / "evidence"
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", source.read_text())
    if forbidden:
        raise SystemExit(f"Forbidden proof-source tokens: {forbidden}")
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    with tempfile.TemporaryDirectory(prefix="jsp-000301-check-") as temp:
        output = Path(temp) / "Counterexample.olean"
        command = [str(lean), "-o", str(output), source.name]
        try:
            result = subprocess.run(command, cwd=source.parent, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    timeout=240)
        except subprocess.TimeoutExpired as error:
            captured = error.stdout or b""
            if isinstance(captured, bytes):
                captured = captured.decode(errors="replace")
            (evidence / "lean-build.log").write_text(
                version + "\n" + captured + "\nTIMEOUT after 240 seconds\n")
            raise SystemExit("Lean compilation timed out; no success claimed")
        log = version + "\n" + result.stdout + f"\nexit_code={result.returncode}\n"
        (evidence / "lean-build.log").write_text(log)
        replay_code = None
        if result.returncode == 0 and output.is_file():
            if "sorryAx" in result.stdout:
                raise SystemExit("Rejected unexpected incomplete-proof dependency")
            checker = lean.with_name("leanchecker")
            environment = dict(os.environ)
            environment["PATH"] = str(lean.parent) + os.pathsep + environment.get("PATH", "")
            environment["LEAN_PATH"] = temp
            replay = subprocess.run(
                [str(checker), "--verbose", "Counterexample"],
                cwd=temp, env=environment, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=120)
            replay_code = replay.returncode
            (evidence / "leanchecker.log").write_text(
                "Same-toolchain kernel replay, not an independent verifier.\n"
                + replay.stdout + f"\nexit_code={replay_code}\n")
        metadata = {
            "checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean_version": version,
            "lean_binary_sha256": sha256(lean),
            "source_sha256": sha256(source),
            "source_bytes": source.stat().st_size,
            "build_log_sha256": sha256(evidence / "lean-build.log"),
            "exit_code": result.returncode,
            "produced_olean": output.is_file(),
            "olean_sha256": sha256(output) if output.is_file() else None,
            "platform": platform.platform(),
            "library": "Lean bundled libraries only; no mathlib",
            "fresh_project_output": True,
            "compiler_and_bundled_libraries_are_prebuilt": True,
            "independent_checker": None,
            "same_toolchain_leanchecker_exit_code": replay_code,
            "network_disabled_by_runner": False,
            "forbidden_source_tokens": forbidden,
        }
        (evidence / "lean-build.json").write_text(json.dumps(metadata, indent=2) + "\n")
        print(log, end="")
        if result.returncode or not output.is_file():
            raise SystemExit(result.returncode or 1)
        if replay_code:
            raise SystemExit(replay_code)


if __name__ == "__main__":
    main()
