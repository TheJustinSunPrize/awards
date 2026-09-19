#!/usr/bin/env python3
"""Clean build, audit the final declarations, and replay the Lean kernel."""
import datetime, hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
lake = shutil.which('lake')
if not lake:
    sys.exit('Install the toolchain in lean-toolchain and put lake on PATH.')
results = []
def run(name, args, timeout=1800):
    print(f'Checking: {name}', flush=True)
    start = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=timeout)
    output = proc.stdout.replace(str(ROOT), '<PROJECT>')
    (OUT / f'{name}.log').write_text(output)
    results.append(dict(name=name, exit_code=proc.returncode,
                        elapsed_seconds=round(time.monotonic()-start, 3)))
    if proc.returncode:
        print(output)
        sys.exit(f'{name} failed')
    return output
version = run('toolchain', [lake, 'env', 'lean', '--version'])
assert 'version 4.34.0,' in version, version
run('clean', [lake, '--no-cache', 'clean'])
run('build', [lake, '--no-cache', 'build'])
audit = run('axioms', [lake, 'env', 'lean', 'JSP500/Audit.lean'])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
checked = {}
for line in audit.splitlines():
    match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
    if match:
        names = set(filter(None, match[2].split(', ')))
        assert names <= allowed, line
        checked[match[1]] = sorted(names)
assert len(checked) == 26, checked
for theorem in ['JSP500.main_proven', 'JSP500.upstream_proven']:
    assert theorem in checked, f'Missing final theorem: {theorem}'
run('kernel-replay', [lake, 'env', 'leanchecker', '--fresh', '--verbose', 'JSP500'])
files = sorted([p.relative_to(ROOT).as_posix() for p in (ROOT/'JSP500').rglob('*.lean')]
               + ['JSP500.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify.py'])
record = dict(checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              language='Lean 4.34.0',
              lean_commit='293d5d0c0c3f3dded4688b3ccd6a33939ac5102b',
              mathlib_commit='5ed2965256430c3649e86755f9576b54eca72435',
              main_theorems=['JSP500.main_proven', 'JSP500.upstream_proven'],
              audited_declarations=checked, checks=results,
              sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files},
              verification_scope='Fresh replay uses the Lean kernel, not an independent kernel implementation. Statement correspondence and prize review remain for reviewers.')
(OUT/'record.json').write_text(json.dumps(record, indent=2)+'\n')
print('PASS: clean build, 26-declaration axiom audit, and fresh kernel replay.', flush=True)
