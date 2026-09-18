#!/usr/bin/env python3
"""Build delivered proofs and enforce the main declarations' axiom allowlist."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
DECLS = {
    'JSP000746.resolution',
    'JSP000746.independent_schur_triple_le_eighteen',
    'JSP000746.erdos_895',
    'JSP000746.erdos_895_finite_interval',
}


def run(args, filename):
    p = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    (EVIDENCE / filename).write_text(p.stdout)
    print(p.stdout, end='')
    if p.returncode:
        raise SystemExit(f'{args} failed: {p.returncode}')
    return p.stdout


def main():
    sources = [ROOT / 'JSP000746.lean', ROOT / 'Audit.lean']
    sources += sorted((ROOT / 'JSP000746').glob('*.lean'))
    forbidden = re.compile(r'\b(sorry|admit|native_decide|bv_decide|bv_check|ofReduceBool|sorryAx|unsafe|implemented_by)\b|^\s*axiom\s', re.M)
    for path in sources:
        if forbidden.search(path.read_text()):
            raise SystemExit(f'Forbidden proof shortcut in {path.relative_to(ROOT)}')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if mathlib['rev'] != '5ed2965256430c3649e86755f9576b54eca72435':
        raise SystemExit('Unexpected Mathlib revision')
    run(['lake', 'build'], 'build.log')
    output = run(['lake', 'env', 'lean', 'Audit.lean'], 'axioms.log')
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        found[name] = {x.strip() for x in axioms.split(',') if x.strip()}
    if set(found) != DECLS:
        raise SystemExit(f'Unexpected audit declarations: {set(found)}')
    for name, axioms in found.items():
        if not axioms <= ALLOW:
            raise SystemExit(f'Nonstandard axioms for {name}: {axioms - ALLOW}')
    files = sources + [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml',
                       ROOT / 'lake-manifest.json', ROOT / 'scripts/generate_rup.py',
                       ROOT / 'scripts/verify.py', EVIDENCE / 'core.cnf',
                       EVIDENCE / 'core.lrat', EVIDENCE / 'schur_core.json']
    (EVIDENCE / 'SHA256SUMS').write_text(''.join(
        f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT)}\n'
        for p in sorted(files)))
    print('PASS: build, source scan, locked dependency, four main axiom closures.')


if __name__ == '__main__':
    main()
