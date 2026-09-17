"""Export requested theorems and recheck their declaration closure with Nanoda."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Callable

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def audit_export(path: Path, required: list[str]) -> dict:
    names = {0: ""}
    declarations: set[str] = set()
    theorems: set[str] = set()
    axioms: set[str] = set()
    metadata = None
    with path.open() as stream:
        for line in stream:
            obj = json.loads(line)
            if "meta" in obj:
                metadata = obj["meta"]
            if "in" in obj:
                item = obj.get("str") or obj.get("num")
                pre = names[item["pre"]]
                part = str(item.get("str", item.get("i")))
                names[obj["in"]] = pre + "." + part if pre else part
            for kind in ["axiom", "def", "thm", "opaque"]:
                if kind in obj:
                    item = obj[kind]
                    name = names[item["name"]]
                    declarations.add(name)
                    if kind == "thm":
                        theorems.add(name)
                    if item.get("isUnsafe", False) or item.get("safety", "safe") != "safe":
                        raise RuntimeError("Unsafe declaration in export: " + name)
                    if kind == "axiom":
                        axioms.add(name)
    if metadata is None or not set(required) <= theorems:
        raise RuntimeError("Export lacks metadata or a requested declaration is not a theorem")
    if metadata.get("format", {}).get("version") != "3.1.0":
        raise RuntimeError("This export auditor supports format 3.1.0 only")
    if not axioms <= ALLOWED:
        raise RuntimeError("Unexpected exported axioms: " + str(sorted(axioms - ALLOWED)))
    return {"metadata": metadata, "axioms": sorted(axioms), "requested_theorems": required,
            "sha256": digest(path), "bytes": path.stat().st_size}


def corrupt_control(source: Path, destination: Path) -> None:
    """Change one theorem's type from True to False while retaining its proof and valid NDJSON."""
    rows = [json.loads(line) for line in source.read_text().splitlines()]
    names = {0: ""}
    false_expr = None
    for obj in rows:
        if "in" in obj:
            item = obj.get("str") or obj.get("num")
            pre = names[item["pre"]]
            part = str(item.get("str", item.get("i")))
            names[obj["in"]] = pre + "." + part if pre else part
        if "const" in obj and names[obj["const"]["name"]] == "False":
            false_expr = obj["ie"]
    if false_expr is None:
        raise RuntimeError("Control export lacks the False type")
    changed = 0
    for obj in rows:
        if "thm" in obj and names[obj["thm"]["name"]] == "ExternalControl.valid":
            obj["thm"]["type"] = false_expr
            changed += 1
    if changed != 1:
        raise RuntimeError("Expected exactly one control theorem to mutate")
    destination.write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))


def check(exporter: Path, checker: Path, lean: Path, modules: list[str], requested: list[str],
          build: Path, results: Path, env: dict[str, str], redact: Callable[[str], str],
          checks: list[dict], lean_commit: str) -> dict:
    def run(name: str, command: list[str], output: Path | None = None,
            negative: bool = False) -> str:
        if output:
            with output.open("w") as stream:
                proc = subprocess.run(command, cwd=build, env=env, text=True,
                                      stdout=stream, stderr=subprocess.PIPE, timeout=600)
            raw = proc.stderr
        else:
            proc = subprocess.run(command, cwd=build, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
            raw = proc.stdout
        text = redact(raw)
        log = results / (name + ".log")
        log.write_text(text)
        checks.append({"name": name, "command": [Path(command[0]).name] +
                       [redact(arg) for arg in command[1:]], "exit_code": proc.returncode,
                       "expected_failure": negative, "log": log.name, "log_sha256": digest(log)})
        print(name + ": exit " + str(proc.returncode), flush=True)
        if negative:
            if proc.returncode == 0 or "assertion failed: self.def_eq(u, v)" not in text:
                raise RuntimeError("Mutated proof did not fail for the required typechecking reason")
        elif proc.returncode:
            raise RuntimeError(name + " failed; see " + log.name)
        return text

    def configuration(label: str, export: Path) -> Path:
        path = build / (label + ".json")
        printer = build / (label + "-axioms.txt")
        printer.write_text("")
        path.write_text(json.dumps({"export_file_path": str(export), "use_stdin": False,
            "permitted_axioms": sorted(ALLOWED), "unpermitted_axiom_hard_error": True,
            "unsafe_permit_all_axioms": False, "num_threads": 2,
            "nat_extension": True, "string_extension": True,
            "pp_output_path": str(printer),
            "print_success_message": True}, indent=2) + "\n")
        return path

    export_path = build / "proofs.ndjson"
    run("export", [str(exporter)] + modules + ["--"] + requested, output=export_path)
    info = audit_export(export_path, requested)
    if info["metadata"]["lean"]["githash"] != lean_commit:
        raise RuntimeError("Export came from a different Lean commit")
    text = run("nanoda", [str(checker), str(configuration("nanoda", export_path))])
    match = re.fullmatch(r"Checked (\d+) declarations with no errors\s*", text)
    if not match:
        raise RuntimeError("Missing unqualified Nanoda success message")
    info.update({"status": "passed", "checked_declarations": int(match.group(1)),
                 "exporter_binary_sha256": digest(exporter), "nanoda_binary_sha256": digest(checker)})

    control = build / "ExternalControl.lean"
    control.write_text("namespace ExternalControl\n"
                      "theorem falseType : False → False := fun h => h\n"
                      "theorem valid : True := True.intro\nend ExternalControl\n")
    run("external-control-compile", [str(lean), "-o", "ExternalControl.olean", control.name])
    correct, corrupt = build / "control.ndjson", build / "corrupt.ndjson"
    run("external-control-export", [str(exporter), "ExternalControl", "--",
        "ExternalControl.falseType", "ExternalControl.valid"], output=correct)
    audit_export(correct, ["ExternalControl.falseType", "ExternalControl.valid"])
    positive_text = run("nanoda-positive-control", [str(checker), str(configuration("correct", correct))])
    if not re.fullmatch(r"Checked (\d+) declarations with no errors\s*", positive_text):
        raise RuntimeError("External positive control lacked unqualified success")
    corrupt_control(correct, corrupt)
    run("nanoda-negative-control", [str(checker), str(configuration("corrupt", corrupt))], negative=True)
    info["positive_control_sha256"] = digest(correct)
    info["negative_control_sha256"] = digest(corrupt)
    info["configuration"] = {
        "permitted_axioms": sorted(ALLOWED), "unpermitted_axiom_hard_error": True,
        "unsafe_permit_all_axioms": False, "num_threads": 2,
        "nat_extension": True, "string_extension": True,
    }
    return info
