#!/usr/bin/env python3
"""Static delivery checks only. No Lean elaboration or kernel execution."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

from common import forbidden_constructs, imported_modules

ROOT = Path(__file__).resolve().parents[1]
FC_FILE = 'FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean'
EXPECTED_FC_BLOB = '08b5da1a82f2e4ad251b18d4c94def8fc715f694'


def main() -> None:
    sources = [ROOT / 'JSP000078.lean', *sorted((ROOT / 'JSP000078').glob('*.lean')),
               ROOT / FC_FILE]
    lines = 0
    for path in sources:
        text = path.read_text(encoding='utf-8')
        forbidden = forbidden_constructs(text)
        if forbidden:
            raise ValueError(f'{path.relative_to(ROOT)}: {forbidden}')
        imported_modules(text)
        lines += len(text.splitlines())
    body = (ROOT / 'JSP000078/GeneralGraph.lean').read_text(encoding='utf-8')
    final_statement = body.split('theorem erdos_58_exact_statement :', 1)[1]
    for excluded in ('[Finite ', '[Fintype ', '[Countable '):
        if excluded in final_statement:
            raise ValueError(f'Unexpected vertex restriction: {excluded}')
    for required in ('G.oddCycleLengths.Finite', 'G.oddCycleLengths.ncard ≤ k',
                     'G.chromaticNumber', '.IsContained G', '↔'):
        if required not in final_statement:
            raise ValueError(f'Missing statement component: {required}')
    b = (ROOT / FC_FILE).read_bytes()
    actual = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
    if actual != EXPECTED_FC_BLOB:
        raise ValueError(f'FC definition source differs: {actual}')
    print(json.dumps({
        'static_checks_passed': True,
        'lean_files_checked': len(sources),
        'lean_lines_checked': lines,
        'fc_source_git_blob_matches': actual,
        'lean_compilation_performed': False,
        'axiom_audit_performed': False,
        'upstream_proof_closure_checked_by_this_script': False,
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError, IndexError) as error:
        print(f'STATIC CHECK FAILED: {error}', file=sys.stderr)
        sys.exit(1)
