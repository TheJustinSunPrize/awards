#!/usr/bin/env python3
"""Run actual Lean verification and record a fail-closed, source-bound receipt.

Each run starts with a NOT_RUN receipt. Only a real successful Lean invocation,
with all expected axiom reports, can produce a passed receipt here.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from audit import audit

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
PIN = 'leanprover/lean4:v4.19.0'
TARGETS = {
    'JSP690.JSP_000690',
    'JSP690.JSP_000690_full',
    'JSP690.Edge.ext_vertices',
    'JSP690.Edge.proper_iff_nonmonochromatic',
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(receipt: dict) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / 'status.json').write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def run(args: list[str], log_name: str) -> str:
    result = subprocess.run(
        args, cwd=ROOT, text=True, encoding='utf-8', errors='replace',
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    (OUT / log_name).write_text(result.stdout, encoding='utf-8')
    print(result.stdout, end='')
    if result.returncode != 0:
        raise RuntimeError(f'Command exited {result.returncode}: {args!r}; see {log_name}')
    return result.stdout


def parse_axioms(log: str) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for name, values in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        found[name] = [x.strip() for x in values.split(',') if x.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        found[name] = []
    missing = TARGETS - found.keys()
    if missing:
        raise RuntimeError(f'Expected axiom reports missing: {sorted(missing)}')
    for name in TARGETS:
        unexpected = set(found[name]) - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(f'Unapproved axioms in {name}: {sorted(unexpected)}')
    return {name: found[name] for name in sorted(TARGETS)}


def main() -> int:
    OUT.mkdir(exist_ok=True)
    receipt = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'lean_status': 'NOT_RUN',
        'pinned_toolchain': PIN,
        'source_file': 'JSP690.lean',
        'source_sha256': sha(ROOT / 'JSP690.lean'),
        'python_audit': 'NOT_RUN',
        'formal_verification_completed': False,
    }
    save(receipt)
    try:
        result = audit()
        (ROOT / 'audit-results.json').write_text(
            json.dumps(result, indent=2) + '\n', encoding='utf-8')
        receipt['python_audit'] = 'PASSED'
        receipt['source_consistency_audit'] = result['source_consistency_audit']['status']
        if (ROOT / 'lean-toolchain').read_text().strip() != PIN:
            raise RuntimeError('Unexpected lean-toolchain pin')
        lake = shutil.which('lake')
        if lake is None:
            receipt['reason'] = 'lake/Lean toolchain is not installed or not on PATH.'
            save(receipt)
            print('NOT RUN: Lean compiler unavailable. Python checks are not a Lean proof.',
                  file=sys.stderr)
            return 2
        version = run([lake, 'env', 'lean', '--version'], 'lean-version.log')
        receipt['lean_version_output'] = version.strip()
        if not re.search(r'\bversion 4\.19\.0(?:[ ,)]|$)', version):
            raise RuntimeError('Lean version does not match the requested 4.19.0 pin')
        receipt['lean_status'] = 'RUNNING'
        save(receipt)
        run([lake, 'clean'], 'lean-clean.log')
        run([lake, 'build'], 'lean-build.log')
        checked = run([lake, 'env', 'lean', 'JSP690.lean'], 'lean-check.log')
        # Reject warnings as well as explicit errors; never accept a sorry warning.
        if re.search(r'\b(?:error|warning):', checked, flags=re.IGNORECASE):
            raise RuntimeError('Lean output contains an error or warning')
        receipt['axiom_dependencies'] = parse_axioms(checked)
        if sha(ROOT / 'JSP690.lean') != receipt['source_sha256']:
            raise RuntimeError('Source changed during verification')
        olean = ROOT / '.lake/build/lib/lean/JSP690.olean'
        if not olean.is_file():
            raise RuntimeError('Expected freshly built JSP690.olean is absent')
        receipt['olean_sha256'] = sha(olean)
        receipt['lean_status'] = 'PASSED_LEAN_ELABORATION_AND_AXIOM_AUDIT'
        receipt['formal_verification_completed'] = True
        receipt['commands'] = [
            'lake env lean --version', 'lake clean', 'lake build',
            'lake env lean JSP690.lean',
        ]
        save(receipt)
        print('PASS: Lean accepted the source and all requested axiom audits passed.')
        return 0
    except (OSError, RuntimeError, AssertionError) as exc:
        receipt['lean_status'] = ('FAILED' if receipt['lean_status'] == 'RUNNING'
                                  else 'NOT_RUN')
        receipt['formal_verification_completed'] = False
        receipt['reason'] = str(exc)
        save(receipt)
        print(f'VERIFICATION DID NOT PASS: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
