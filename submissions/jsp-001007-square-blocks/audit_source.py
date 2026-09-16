#!/usr/bin/env python3
"""Conservative source hygiene check. Passing is NOT Lean verification."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


def active_code(text: str) -> str:
    """Mask Lean's nested block comments, line comments, and string literals."""
    out = list(text)
    i, depth = 0, 0
    line_comment = False
    string = False
    while i < len(text):
        c = text[i]
        if line_comment:
            if c == "\n":
                line_comment = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if c == "\\" and i + 1 < len(text):
                out[i:i+2] = "  "
                i += 2
            else:
                if c == '"':
                    string = False
                if c != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            out[i:i+2] = "  "
            line_comment = True
            i += 2
        elif c == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment or string")
    return "".join(out)


EXPECTED_IMPORTS = {
    "JSP001007.lean": ["Mathlib", "JSP001007.Arithmetic", "JSP001007.PrimeBlocks"],
    "PrimeBlocks.lean": ["Mathlib"],
    "Arithmetic.lean": ["Lean"],
    "JSP001007Standalone.lean": ["Mathlib"],
}
EXPECTED_REPORT_COUNTS = {"JSP001007.lean": 5, "Arithmetic.lean": 7,
                          "PrimeBlocks.lean": 2, "JSP001007Standalone.lean": 14}


def inspect(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    code = active_code(text)
    forbidden = r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|ofReduceBool|trustCompiler|skipKernelTC)\b"
    matches = [m.group() for m in re.finditer(forbidden, code)]
    imports = re.findall(r"^\s*import\s+(\S+)", code, re.M)
    names = re.findall(r"^\s*(?:private\s+)?(?:theorem|lemma)\s+(\w+)", code, re.M)
    reports = re.findall(r"^\s*#print\s+axioms\s+(\S+)", code, re.M)
    passed = (not matches and imports == EXPECTED_IMPORTS.get(path.name)
              and len(reports) == EXPECTED_REPORT_COUNTS.get(path.name))
    return {
        "file": path.name, "passed": passed,
        "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "line_count": len(text.splitlines()), "theorem_and_lemma_count": len(names),
        "forbidden_active_tokens": matches, "imports": imports,
        "requested_axiom_reports": reports,
    }


def main() -> int:
    root = Path(__file__).resolve().parent
    paths = ([Path(p) for p in sys.argv[1:]] if len(sys.argv) > 1 else
             [root / "JSP001007.lean", root / "JSP001007/Arithmetic.lean", root / "JSP001007/PrimeBlocks.lean",
              root / "JSP001007Standalone.lean"])
    results = [inspect(p) for p in paths]
    passed = bool(results) and all(r["passed"] for r in results)
    print(json.dumps({
        "status": "PASS: source hygiene only" if passed else "FAIL: source hygiene",
        "lean_kernel_status": "NOT_CHECKED_BY_THIS_SCRIPT", "files": results,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
