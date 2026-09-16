#!/usr/bin/env python3
"""Fail-closed audit of compiler diagnostics and transitive axiom reports.

This program does NOT invoke Lean. The caller must first require the same
compiler invocation to exit successfully. --wasm additionally checks the
recorded IO tag, boxed return value, and diagnostic-error flag.
"""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path

MAIN = {
    "JSP001007.counterexamples",
    "JSP001007.not_uniform_tenth_sieve",
    "JSP001007.not_erdos_uniform_sieve",
    "JSP001007.not_erdos_eventual_uniform_sieve",
    "JSP001007.fixed_1000_counterexample",
}
PRIMES = {
    "JSP001007.primeBlock_card_unbounded",
    "JSP001007.large_primeBlock",
}
CORE = {"JSP001007.Arithmetic." + n for n in (
    "window_point_mod", "window_point_in_interval", "window_points_injective",
    "window_density", "cluster_conditions", "cluster_cutoff_four", "cutoff_ten",
)}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def audit(text: str, expected: set[str], wasm: bool = False) -> dict:
    lines = []
    diagnostics = []
    wasm_results = []
    for line in text.splitlines():
        if line.startswith("COMPILE_STATUS "):
            wasm_results.append(json.loads(line.removeprefix("COMPILE_STATUS ")))
        try:
            data = json.loads(line)
        except (json.JSONDecodeError, ValueError):
            lines.append(line)
            continue
        if isinstance(data, dict) and "severity" in data:
            diagnostics.append(data)
            lines.append(str(data.get("data", "")))
        else:
            lines.append(line)
    normalized = "\n".join(lines)
    if any(d["severity"] == "error" for d in diagnostics):
        raise ValueError("Compiler emitted an error diagnostic")
    if re.search(r"\bsorryAx\b|declaration uses.*sorry|\berror:", normalized):
        raise ValueError("Compiler log contains a forbidden dependency/error")
    if wasm:
        expected_status = {"ioTag": 0, "returnValue": 0, "hasLeanErrors": False}
        if wasm_results != [expected_status]:
            raise ValueError(f"Invalid/missing WASM completion status: {wasm_results}")
        if "SEARCH_PATH_STATUS 0" not in text or "SNAPSHOT_STATUS 0 0" not in text:
            raise ValueError("Missing successful runtime/snapshot initialization")
    reports: dict[str, set[str]] = {}
    name = r"JSP001007(?:\.[A-Za-z_][A-Za-z_0-9]*)+"
    pattern = rf"['\"]?({name})['\"]?\s+depends on axioms:\s*\[([^\]]*)\]"
    for match in re.finditer(pattern, normalized, re.S):
        n, raw = match.groups()
        if n in reports:
            raise ValueError(f"Duplicate axiom report: {n}")
        reports[n] = {s.strip().strip("'\"") for s in raw.split(",") if s.strip()}
    empty = rf"['\"]?({name})['\"]?\s+does not depend on any axioms"
    for match in re.finditer(empty, normalized):
        n = match.group(1)
        if n in reports:
            raise ValueError(f"Duplicate axiom report: {n}")
        reports[n] = set()
    if set(reports) != expected:
        raise ValueError(f"Missing/unexpected reports: found {sorted(reports)}")
    bad = {n: sorted(a - ALLOWED) for n, a in reports.items() if a - ALLOWED}
    if bad:
        raise ValueError(f"Nonstandard transitive dependencies: {bad}")
    return {
        "status": "PASS: expected transitive axiom reports use only standard permitted axioms",
        "reports": {n: sorted(reports[n]) for n in sorted(reports)},
        "wasm_completion_status_checked": wasm,
        "precondition": "The same compiler invocation must have exited with code 0",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--scope", choices=("main", "core", "primes", "all"), default="main")
    parser.add_argument("--wasm", action="store_true")
    args = parser.parse_args()
    expected = {"main": MAIN, "core": CORE, "primes": PRIMES, "all": MAIN | CORE | PRIMES}[args.scope]
    try:
        report = audit(args.log.read_text(encoding="utf-8"), expected, args.wasm)
    except (ValueError, OSError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}, indent=2))
        return 1
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
