#!/usr/bin/env python3
"""Rebuild, audit theorem dependencies, replay the kernel, and cross-check data."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
env = os.environ.copy()
local = ROOT / '.tools' / 'lean-4.34.0-darwin_aarch64' / 'bin'
if local.is_dir():
    env['PATH'] = str(local) + os.pathsep + env.get('PATH', '')
lake = shutil.which('lake', path=env.get('PATH'))
if not lake:
    sys.exit('Install the toolchain in lean-toolchain, then rerun this script.')
results = []

def run(name, args, timeout=180):
    print(f'Checking: {name}', flush=True)
    start = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=timeout)
    output = proc.stdout.replace(str(ROOT), '<PROJECT>')
    (OUT / f'{name}.log').write_text(output)
    results.append({'name': name, 'exit_code': proc.returncode,
                    'elapsed_seconds': round(time.monotonic()-start, 3)})
    if proc.returncode:
        print(output)
        sys.exit(f'{name} failed with exit code {proc.returncode}')
    return output

version = run('toolchain', [lake, 'env', 'lean', '--version'])
assert 'version 4.34.0,' in version, version
run('clean', [lake, 'clean'])
build = run('build', [lake, 'build'])
assert 'warning:' not in build.lower(), build
audit = run('axioms', [lake, 'env', 'lean', 'Audit.lean'])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for line in audit.splitlines():
    if 'depends on axioms:' in line:
        names = set(re.search(r'\[(.*)\]', line).group(1).split(', '))
        assert names <= allowed, line
assert "'JSP653.exact_formula_false' depends on axioms: [propext, Quot.sound]" in audit
run('kernel-replay', [lake, 'env', 'leanchecker', '--fresh', '--verbose', 'JSP653'])
run('witness', [sys.executable, 'scripts/check_witness.py'])
source_files = ['JSP653.lean','Audit.lean','lean-toolchain','lakefile.toml',
                'lake-manifest.json','scripts/check_witness.py','scripts/verify.py']
record = {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'language': 'Lean 4.34.0',
    'lean_commit': '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b',
    'dependencies': 'Bundled Lean/Std only; no external Lake packages',
    'main_theorem': 'JSP653.exact_formula_false',
    'main_theorem_axioms': ['propext','Quot.sound'],
    'checks': results,
    'sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in source_files},
    'limitations': [
        'leanchecker uses the same Lean kernel; it is not an independent implementation.',
        'Python enumeration cross-checks data; it is not the formal proof.',
        'No independent human statement review or official prize verification is claimed.',
    ],
}
(OUT / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: clean build, axiom audit, fresh kernel replay, independent enumeration.', flush=True)
