#!/usr/bin/env python3
"""Compile a target, replay its kernel, export named theorem closures and run Nanoda.

This is local reproduction evidence, not an official prize verification record.
The output reports actual exit codes and does not claim network isolation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import socket
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
WORK = HERE.parent
LEAN_BIN = WORK / "lean-k8/toolchain/lean-4.33.1-darwin_aarch64/bin"
EXPORT = HERE / "lean4export/.lake/build/bin/lean4export"
NANODA = HERE / "bin/nanoda_bin"
NETWORK_PROFILE = "(version 1)(allow default)(deny network*)"


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def local_module_order(project, target):
    """Find ordinary local imports and return them in dependency-first order."""
    ordered, visiting, visited = [], set(), set()

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise SystemExit(f"Local import cycle: {module}")
        source = project / Path(*module.split(".")).with_suffix(".lean")
        if not source.is_file():
            return
        visiting.add(module)
        for line in source.read_text().splitlines():
            match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", line)
            if match:
                for imported in match.group(1).split("--", 1)[0].split():
                    visit(imported)
        visiting.remove(module)
        visited.add(module)
        ordered.append((module, source))

    visit(target)
    return ordered


def network_denial_probe(sandbox):
    """Compare a reachable loopback socket with the same connection under the policy."""
    code = ("import socket,sys\n"
            "s=socket.socket(); s.settimeout(3)\n"
            "try:\n s.connect(('127.0.0.1',int(sys.argv[1])))\n"
            "except PermissionError as e:\n print('NETWORK_DENIED',e.errno); sys.exit(73)\n"
            "print('NETWORK_ACCESSIBLE')\n")
    records = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(3)
        port = str(listener.getsockname()[1])
        for name, prefix in [("control", []), ("denied", [str(sandbox), "-p", NETWORK_PROFILE])]:
            child = subprocess.run(prefix + [sys.executable, "-c", code, port],
                                   capture_output=True, text=True, timeout=10)
            records.append({"name": name, "exit_code": child.returncode,
                            "stdout": child.stdout, "stderr": child.stderr})
    if not (records[0]["exit_code"] == 0 and records[0]["stdout"].strip() == "NETWORK_ACCESSIBLE"
            and records[1]["exit_code"] == 73 and "NETWORK_DENIED" in records[1]["stdout"]):
        raise SystemExit("Network-denial control failed: " + json.dumps(records))
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--theorem", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--lean-bin", type=Path, default=LEAN_BIN,
                        help="Directory containing the matching lean, lake, and leanchecker binaries")
    parser.add_argument("--exporter", type=Path, default=EXPORT,
                        help="lean4export binary built for that exact Lean version")
    parser.add_argument("--nanoda", type=Path, default=NANODA)
    parser.add_argument("--deny-network", action="store_true",
                        help="On macOS, wrap every proof-checking command in sandbox-exec deny network*")
    parser.add_argument("--skip-kernel-replay", action="store_true")
    args = parser.parse_args()
    project = args.project.resolve()
    output = args.output.resolve()
    lean_bin = args.lean_bin.resolve()
    exporter = args.exporter.resolve()
    nanoda = args.nanoda.resolve()
    output.mkdir(parents=True, exist_ok=True)
    module_path = Path(*args.module.split("."))
    source = project / module_path.with_suffix(".lean")
    olean = project / ".lake/build/lib/lean" / module_path.with_suffix(".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    if not source.is_file():
        raise SystemExit(f"No source: {source}")
    modules = local_module_order(project, args.module)
    command_prefix = []
    network_probe = None
    if args.deny_network:
        sandbox = Path("/usr/bin/sandbox-exec")
        if not sandbox.is_file():
            raise SystemExit("--deny-network requires /usr/bin/sandbox-exec; no unchecked fallback")
        network_probe = network_denial_probe(sandbox)
        command_prefix = [str(sandbox), "-p", NETWORK_PROFILE]
    env = os.environ.copy()
    env["PATH"] = str(lean_bin) + os.pathsep + env.get("PATH", "")
    lean_version = subprocess.check_output(command_prefix + [str(lean_bin / "lean"), "--version"],
                                          env=env, text=True).strip()
    project_toolchain = (project / "lean-toolchain").read_text().strip()
    required_version = re.search(r":v(\d+\.\d+\.\d+(?:-rc\d+)?)$", project_toolchain)
    actual_version = re.search(r"version (\d+\.\d+\.\d+(?:-rc\d+)?)", lean_version)
    if required_version and (not actual_version or required_version[1] != actual_version[1]):
        raise SystemExit(f"Toolchain mismatch: project requires {project_toolchain}; binary is {lean_version}")
    commands = []
    result = {
        "module": args.module,
        "theorems": args.theorem,
        "source_sha256": sha(source),
        "source_bytes": source.stat().st_size,
        "local_sources": [{"module": name, "path": str(path), "sha256": sha(path)}
                          for name, path in modules],
        "toolchain": lean_version,
        "project_lean_toolchain": project_toolchain,
        "verification_script_sha256": sha(Path(__file__)),
        "lean_bin": str(lean_bin),
        "lean_sha256": sha(lean_bin / "lean"),
        "nanoda_path": str(nanoda),
        "nanoda_sha256": sha(nanoda),
        "exporter_path": str(exporter),
        "exporter_sha256": sha(exporter),
        "commands": commands,
        "network_access_denied_for_check_commands": args.deny_network,
        "network_policy": NETWORK_PROFILE if args.deny_network else None,
        "network_policy_control_probe": network_probe,
        "filesystem_isolated": False,
        "dependencies_rebuilt_from_source": False,
        "precompiled_dependencies_used": True,
        "official_acceptance": False,
    }
    manifest = project / "lake-manifest.json"
    if manifest.is_file():
        result["lake_manifest_sha256"] = sha(manifest)
        result["lake_manifest"] = json.loads(manifest.read_text())

    def save():
        (output / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
        substitutions = sorted([(str(project), "<project>"), (str(lean_bin), "<lean-bin>"),
                                (str(exporter), "<exporter>"), (str(nanoda), "<nanoda>"),
                                (str(output), "<verification-output>"),
                                (str(HERE.parent.parent), "<workspace>")],
                               key=lambda item: len(item[0]), reverse=True)

        def public(value):
            if isinstance(value, str):
                for old, new in substitutions:
                    value = value.replace(old, new)
                return value
            if isinstance(value, list):
                return [public(item) for item in value]
            if isinstance(value, dict):
                return {key: public(item) for key, item in value.items()}
            return value

        public_result = public(result)
        public_result["paths_redacted_for_publication"] = True
        (output / "verification.public.json").write_text(json.dumps(public_result, indent=2) + "\n")

    def run(name, command, stdout_name=None):
        command = command_prefix + command
        start = time.monotonic()
        stdout = output / (stdout_name or name + ".stdout.log")
        stderr = output / (name + ".stderr.log")
        with stdout.open("wb") as out, stderr.open("wb") as err:
            process = subprocess.Popen(command, cwd=project, env=env, stdout=out,
                                       stderr=err, start_new_session=True)
            try:
                code = process.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                code = 124
        commands.append({"name": name, "command": command, "exit_code": code,
                         "seconds": round(time.monotonic() - start, 3)})
        save()
        if code != 0:
            raise SystemExit(f"{name} failed ({code}); see {output}")

    lake = str(lean_bin / "lake")
    for name, path in modules:
        artifact = project / ".lake/build/lib/lean" / Path(*name.split(".")).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run("compile-" + name, [lake, "env", "lean", "-o", str(artifact), str(path)])
    if not args.skip_kernel_replay:
        run("leanchecker", [lake, "env", "leanchecker", "--fresh", args.module])
    else:
        result["kernel_replay_skipped"] = True
    exported = output / "proof.ndjson"
    run("export", [lake, "env", str(exporter), args.module, "--", *args.theorem],
        "proof.ndjson")
    config = {
        "export_file_path": str(exported),
        "use_stdin": False,
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "unpermitted_axiom_hard_error": True,
        "unsafe_permit_all_axioms": False,
        "nat_extension": True,
        "string_extension": True,
        "num_threads": args.threads,
        "pp_to_stdout": True,
        "pp_declars": args.theorem,
        "print_axioms": True,
        "print_success_message": True,
    }
    config_path = output / "nanoda.json"
    config_path.write_text(json.dumps(config, indent=2) + "\n")
    run("nanoda", [str(nanoda), str(config_path)])
    result["export_sha256"] = sha(exported)
    result["export_bytes"] = exported.stat().st_size
    if any(sha(Path(entry["path"])) != entry["sha256"] for entry in result["local_sources"]):
        result["source_changed_during_verification"] = True
        save()
        raise SystemExit("A local source changed during verification; rerun when source is stable")
    result["local_checks_passed"] = True
    save()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
