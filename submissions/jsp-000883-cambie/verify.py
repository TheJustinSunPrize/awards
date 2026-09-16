"""Build, recompile, audit statements and axioms, run negative tests, and replay Lean."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAMES = [
    "Erdos1063.choose_pred_eq_prod",
    "Erdos1063.cambie_witness",
    "Erdos1063.erdos_1063.variants.cambie_upper_bound",
    "Erdos1063.definition_alignment",
    "Erdos1063.target_alignment",
]


def source_hashes() -> dict[str, str]:
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in ROOT.iterdir() if p.is_file() and
            (p.suffix in (".lean", ".toml", ".py") or
             p.name in ("lean-toolchain", "lake-manifest.json"))}


def audit_axioms(text: str, names: list[str]) -> dict[str, list[str]]:
    found = {}
    for name in names:
        pattern = rf"'{re.escape(name)}' depends on axioms:\s*\[([^\]]*)\]"
        matches = re.findall(pattern, text)
        empty = f"'{name}' does not depend on any axioms" in text
        if len(matches) != 1 and not (not matches and empty):
            raise RuntimeError(f"Missing or ambiguous axiom report: {name}")
        axioms = set(filter(None, re.split(r"[\s,]+", matches[0].strip()))) if matches else set()
        forbidden = axioms - ALLOWED
        if forbidden:
            raise RuntimeError(f"Rejected axioms for {name}: {sorted(forbidden)}")
        found[name] = sorted(axioms)
    return found


def without_comments(source: str) -> str:
    result, i, depth = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise RuntimeError("Unterminated comment")
    return "".join(result)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def atomic_json(path: Path, contents: dict) -> None:
    """Replace a JSON record only after a complete sibling file is flushed."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=f".{path.name}.", suffix=".tmp",
                                         delete=False) as handle:
            temporary = Path(handle.name)
            json.dump(contents, handle, indent=2, ensure_ascii=False)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--no-local-toolchain", action="store_true",
                        help="Disable automatic use of the workspace-local Lean toolchain")
    parser.add_argument("--history-dir", type=Path,
                        help="Private archive directory (default: .verification-history)")
    parser.add_argument("--command-timeout", type=float, default=1200,
                        help="Maximum seconds for each verification command (default: 1200)")
    parser.add_argument("--check-axioms-log", type=Path)
    parser.add_argument("--names", nargs="+")
    args = parser.parse_args()
    if args.check_axioms_log:
        try:
            print(json.dumps(audit_axioms(args.check_axioms_log.read_text(encoding="utf-8"),
                                          args.names or NAMES)))
            return 0
        except (RuntimeError, OSError) as error:
            print(error)
            return 2

    logs = ROOT / "logs"
    commands = []
    results = {"run_id": uuid.uuid4().hex, "status": "RUNNING", "started_utc": utc_now(),
               "allowed_axioms": sorted(ALLOWED), "commands": commands}
    transcript = None
    exit_code = 1

    def persist() -> None:
        atomic_json(logs / "results.json", results)

    def run(label: str, command: list[str], *, expected: int | None = 0,
            cwd: Path = ROOT) -> subprocess.CompletedProcess:
        print(label, flush=True)
        transcript.write(f"\n$ {subprocess.list2cmdline(command)}\nCWD: {cwd}\n")
        transcript.flush()
        record = {"label": label, "command": command, "cwd": str(cwd),
                  "started_utc": utc_now(), "status": "RUNNING", "exit_code": None}
        commands.append(record)
        persist()
        output = ""
        try:
            outcome = subprocess.run(command, cwd=cwd, env=env, text=True, encoding="utf-8",
                                     errors="replace", stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, timeout=args.command_timeout)
            output = outcome.stdout
            record.update(status="COMPLETED", exit_code=outcome.returncode)
        except subprocess.TimeoutExpired as error:
            partial = error.stdout or ""
            output = partial.decode("utf-8", errors="replace") if isinstance(partial, bytes) else partial
            record.update(status="TIMED_OUT", error=str(error), timeout_seconds=args.command_timeout)
            raise
        except BaseException as error:
            record.update(status="ERROR", error=f"{type(error).__name__}: {error}")
            raise
        finally:
            record["finished_utc"] = utc_now()
            footer = f"\nCOMMAND STATUS: {record['status']}\nEXIT: {record['exit_code']}\n"
            if "error" in record:
                footer += f"ERROR: {record['error']}\n"
            (logs / f"{label}.log").write_text(output + footer, encoding="utf-8")
            transcript.write(output + footer)
            transcript.flush()
            persist()
        if expected is not None and outcome.returncode != expected:
            raise RuntimeError(f"{label} exited {outcome.returncode}; see logs/{label}.log")
        return outcome

    try:
        logs.mkdir(exist_ok=True)
        if any(logs.iterdir()):
            history = (args.history_dir or ROOT / ".verification-history").resolve()
            if history == logs.resolve() or logs.resolve() in history.parents:
                raise RuntimeError("The private history directory must be outside logs")
            archive = history / results["run_id"] / "logs"
            archive.parent.mkdir(parents=True, exist_ok=False)
            shutil.move(str(logs), str(archive))
            logs.mkdir()
            results["previous_logs_archive"] = str(archive)
        persist()
        transcript = (logs / "verification.log").open("w", encoding="utf-8")
        transcript.write(f"RUN ID: {results['run_id']}\nSTARTED UTC: {results['started_utc']}\n")
        transcript.flush()
        if args.command_timeout <= 0:
            raise RuntimeError("--command-timeout must be positive")
        env = os.environ.copy()
        local_bin = ROOT.parent.parent / "work/environment/lean-4.33.1-windows/bin"
        lean_bin = args.lean_bin
        if (not args.no_local_toolchain and lean_bin is None
                and not shutil.which("lake") and local_bin.is_dir()):
            lean_bin = local_bin
        if lean_bin:
            env["PATH"] = str(lean_bin.resolve()) + os.pathsep + env.get("PATH", "")
        lake = shutil.which("lake", path=env.get("PATH", ""))
        if not lake:
            raise RuntimeError("Lake not found; install the pinned toolchain or pass --lean-bin")
        initial_hashes = source_hashes()
        version = run("lean-version", [lake, "env", "lean", "--version"]).stdout
        if not re.search(r"version 4\.33\.1\b", version):
            raise RuntimeError("Wrong Lean version")
        run("lake-version", [lake, "--version"])
        lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        actual_deps = {}
        for dependency in lock["packages"]:
            if dependency["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", dependency["rev"]):
                raise RuntimeError(f"Unpinned dependency: {dependency['name']}")
            name = dependency["name"]
            directory = ROOT / lock["packagesDir"] / name
            rev = run(f"revision-{name}", ["git", "rev-parse", "HEAD"], cwd=directory).stdout.strip()
            if rev != dependency["rev"]:
                raise RuntimeError(f"Dependency revision mismatch: {name}")
            run(f"clean-{name}", ["git", "diff", "--exit-code", "HEAD"], cwd=directory)
            status = run(f"status-{name}", ["git", "status", "--porcelain", "--untracked-files=normal"],
                         cwd=directory).stdout
            if status.strip():
                raise RuntimeError(f"Modified or untracked dependency files: {name}")
            actual_deps[name] = {"url": dependency["url"], "rev": rev}
        results["dependencies"] = actual_deps
        for filename in ("Statement.lean", "Cambie.lean", "Audit.lean"):
            source = without_comments((ROOT / filename).read_text(encoding="utf-8"))
            bad = re.search(r"\b(sorry|admit|axiom|unsafe|extern|native_decide|ofReduceBool)\b", source)
            if bad:
                raise RuntimeError(f"Source scan rejected {filename}: {bad.group()}")
        results["source_scan"] = "PASS (separate from dependency axiom audit)"
        run("build", [lake, "build"])
        for module in ("Statement", "Cambie", "Audit"):
            run(f"recompile-{module}", [lake, "env", "lean", "-o",
                f".lake/build/lib/lean/{module}.olean", f"{module}.lean"])
        audit = (logs / "recompile-Audit.log").read_text(encoding="utf-8")
        results["axioms"] = audit_axioms(audit, NAMES)
        run("axiom-gate", [sys.executable, str(Path(__file__).resolve()),
            "--check-axioms-log", str(logs / "recompile-Audit.log")])

        temporary = ROOT / "verification-tmp"
        temporary.mkdir(exist_ok=True)
        tests = {
            "false-arithmetic": "example : (2 : Nat) + 2 = 5 := by decide\n",
            "sorry": "theorem negative : False := by sorry\n#print axioms negative\n",
            "custom-axiom": "axiom unapproved : False\ntheorem negative : False := unapproved\n#print axioms negative\n",
        }
        for name, contents in tests.items():
            path = temporary / f"{name}.lean"
            path.write_text(contents, encoding="utf-8")
            result = run(f"negative-{name}", [lake, "env", "lean", str(path)], expected=None)
            if name == "false-arithmetic":
                if result.returncode == 0:
                    raise RuntimeError("False arithmetic unexpectedly compiled")
            else:
                if result.returncode != 0:
                    raise RuntimeError(f"Negative axiom fixture did not elaborate: {name}")
                run(f"reject-{name}", [sys.executable, str(Path(__file__).resolve()),
                    "--check-axioms-log", str(logs / f"negative-{name}.log"),
                    "--names", "negative"], expected=2)
        results["negative_tests"] = "PASS; fixtures are not imported by the proof"
        run("kernel-replay", [lake, "env", "leanchecker", "--fresh", "-v", "Cambie"])
        results["kernel_replay"] = "PASS: same Lean kernel; fresh environment including imports; unsafe/partial declarations skipped by the official tool"
        results["independent_checker"] = "NOT RUN: no second kernel implementation installed"
        if initial_hashes != source_hashes():
            raise RuntimeError("Project source or configuration changed during verification")
        results["source_sha256"] = initial_hashes
        results["status"] = "PASS"
        print("PASS: build, fresh project compilation, type/axiom audit, negative tests, kernel replay.")
        exit_code = 0
    except BaseException as error:
        results["status"] = "FAIL"
        results["error"] = f"{type(error).__name__}: {error}"
        print(f"FAIL: {error}", file=sys.stderr)
    finally:
        results["finished_utc"] = utc_now()
        results["process_exit_code"] = exit_code
        if transcript is not None:
            try:
                transcript.write(f"\nFINAL STATUS: {results['status']}\n"
                                 f"FINISHED UTC: {results['finished_utc']}\n")
                if "error" in results:
                    transcript.write(f"ERROR: {results['error']}\n")
                transcript.close()
            except OSError as error:
                exit_code = 1
                results.update(status="FAIL", process_exit_code=1,
                               transcript_error=f"{type(error).__name__}: {error}")
                print(f"FAIL: could not close transcript: {error}", file=sys.stderr)
        try:
            persist()
        except OSError as error:
            exit_code = 1
            print(f"FAIL: could not publish latest results: {error}", file=sys.stderr)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
