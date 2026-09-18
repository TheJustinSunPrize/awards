"""Run pinned Lake checks and write small public verification records."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    for source_file in ['LcmCounting.lean', 'LcmLiminf.lean']:
        source = (ROOT / source_file).read_text(encoding='utf-8')
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', source):
            raise RuntimeError(f'Unexpected proof construct in {source_file}')
    OUT.mkdir(exist_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Install the pinned Lean/Lake toolchain first')
    checks = []
    counting = {'mem_goodIndices_iff', 'counting_bound', 'counting_bound_sqrt'}
    complete = {'mem_real_count_iff', 'normalized_count_bounded', 'sharp_liminf', 'original_problem'}
    for name, args, expected in [
        ('lean-version.txt', ['env', 'lean', '--version'], set()),
        ('lake-build.txt', ['build'], counting | complete),
        ('lean-trust0.txt', ['env', 'lean', '--trust=0', 'LcmCounting.lean'], counting),
        ('liminf-trust0.txt', ['env', 'lean', '--trust=0', 'LcmLiminf.lean'], complete),
    ]:
        p = subprocess.run([lake, *args], cwd=ROOT, encoding='utf-8',
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=600)
        (OUT / name).write_text(p.stdout, encoding='utf-8', newline='\n')
        print(p.stdout, end='', flush=True)
        if p.returncode:
            raise RuntimeError(f'{name} failed: {p.returncode}')
        if name == 'lean-version.txt':
            if 'Lean (version 4.19.0,' not in p.stdout:
                raise RuntimeError('Toolchain version mismatch')
        else:
            reports = re.findall(r"'JSP000359\.([^']+)' depends on axioms: \[([^]]*)\]", p.stdout)
            if {n for n, _ in reports} != expected:
                raise RuntimeError('Missing theorem audit')
            for _, ax in reports:
                if not set(a.strip() for a in ax.split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}:
                    raise RuntimeError(f'Unexpected axioms: {ax}')
        checks.append({'command': ['lake', *args], 'log': name,
                       'exit_code': p.returncode, 'sha256': digest(OUT / name)})
    files = ['LcmCounting.lean', 'LcmLiminf.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py']
    evidence = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'problem': 'JSP-000359 / Erdos 440',
        'scope': 'Both original questions: real-threshold O(sqrt x) bound and greatest attainable liminf equal to 1',
        'lean': '4.19.0',
        'mathlib': 'c44e0c8ee63ca166450922a373c7409c5d26b00b',
        'files': {name: digest(ROOT / name) for name in files},
        'checks': checks,
        'environment': 'Windows; pinned existing dependency checkouts and compiled cache',
        'independent_checker': False,
        'network_isolated': False,
        'official_review': 'not completed',
        'priority': 'not asserted',
    }
    (OUT / 'verification.json').write_text(json.dumps(evidence, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
