#!/usr/bin/env python3
"""Check ACTUAL output of `lake env lean JSP000078/Audit.lean`.

This parser is a safety gate, not a theorem prover. Passing mock tests of this
script provides no evidence that any Lean theorem compiles.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

EXPECTED = (
    'JSP000078.colorable_of_finite_induced',
    'Erdos58.erdos_58',
    'JSP000078.oddCycleLengths_alignment',
    'JSP000078.erdos_58_exact_statement',
)
ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})


def parse_and_validate(text: str) -> dict[str, list[str]]:
    if re.search(r'\b(?:sorryAx|error)\b', text, re.I):
        raise ValueError('Audit log contains an error or sorryAx')
    results: dict[str, list[str]] = {}
    for name in EXPECTED:
        prefix = r"['‘]?" + re.escape(name) + r"['’]?\s+"
        matches = re.findall(prefix + r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
        empty_matches = re.findall(prefix + r'does not depend on any axioms', text)
        if len(matches) + len(empty_matches) != 1:
            raise ValueError(f'Expected exactly one actual axiom report for {name}')
        axioms = sorted(set(a.strip() for a in matches[0].split(',') if a.strip())) if matches else []
        unexpected = set(axioms) - ALLOWED
        if unexpected:
            raise ValueError(f'{name} depends on unapproved axioms: {sorted(unexpected)}')
        results[name] = axioms
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--json-output', type=Path)
    args = parser.parse_args()
    reports = parse_and_validate(args.log.read_text(encoding='utf-8'))
    result = {'audit_log_accepted': True, 'reports': reports}
    if args.json_output:
        args.json_output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError) as error:
        print(f'AXIOM AUDIT FAILED: {error}', file=sys.stderr)
        sys.exit(1)
