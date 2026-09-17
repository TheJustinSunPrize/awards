"""Check every supplied source module and the final nine/ten-point theorem."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import argparse
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'lean434'
OUT = ROOT / 'verification'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume', action='store_true', help='Reuse only matching local source/output/log checkpoints')
    options = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Put the pinned Lean 4.34.0 toolchain on PATH')
    base_record = json.loads((BASE / 'verification/result.json').read_text(encoding='utf-8'))
    for name, expected in base_record['files'].items():
        if digest(BASE / name) != expected:
            raise RuntimeError('Sibling package changed since verification: ' + name)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    dependencies = {}
    for package in manifest['packages']:
        if package['type'] == 'path':
            if package['name'] != 'jsp404integration' or (ROOT / package['dir']).resolve() != BASE.resolve():
                raise RuntimeError('Unexpected path dependency')
            dependencies[package['name']] = {'path': '../lean434', 'files': base_record['files']}
            continue
        if package['type'] != 'git':
            raise RuntimeError('Unexpected dependency kind')
        directory = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                        cwd=directory, text=True).strip()
        if revision != package['rev'] or dirty:
            raise RuntimeError('Dependency revision/cleanliness mismatch: ' + package['name'])
        dependencies[package['name']] = revision
    modules = json.loads((ROOT / 'modules.json').read_text(encoding='utf-8'))
    if len(modules) != 57 or len({item['module'] for item in modules}) != 57:
        raise RuntimeError('Expected 57 distinct source modules')
    expected_audits = {}
    for item in modules:
        name = item['module']
        source = (ROOT / (name + '.lean')).read_text(encoding='utf-8')
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', source):
            raise RuntimeError('Unexpected proof construct: ' + name)
        names = re.findall(r'^#print axioms ([\w.]+)', source, re.M)
        if not names and name != 'NineCNFDirectAll':
            raise RuntimeError('Missing dependency audit: ' + name)
        if name == 'NineCNFDirectAll' and any(line and not line.startswith('import ') for line in source.splitlines()):
            raise RuntimeError('Unexpected aggregator content')
        expected_audits[name] = {n if '.' in n else item['namespace'] + '.' + n for n in names}
    commands = [
        ('version', ['env', 'lean', '--version'], None),
        ('sibling-build', ['--dir', str(BASE), 'build'], None),
    ]
    output = ROOT / '.lake/build/lib/lean'
    output.mkdir(parents=True, exist_ok=True)
    commands += [(item['module'] + '-trust0',
                  ['env', 'lean', '--trust=0', '-j1' if item['module'] in ['NinePropositionalTrial', 'NineModelTrial', 'NinePointExactTrial'] else '-j4', '-M5000', '-o',
                   '.lake/build/lib/lean/' + item['module'] + '.olean', item['module'] + '.lean'],
                  expected_audits[item['module']]) for item in modules]
    checks = []
    checkpoint_path = ROOT / '.lake/verification-progress.json'
    checkpoint = json.loads(checkpoint_path.read_text()) if options.resume and checkpoint_path.exists() else {}
    def audit(label, stdout, expected):
        if expected is None:
            return
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", stdout)
        audits += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", stdout)]
        if {name for name, _ in audits} != expected:
            raise RuntimeError('Audit coverage mismatch: ' + label)
        for name, axioms in audits:
            if {a.strip() for a in axioms.split(',') if a.strip()} - ALLOWED:
                raise RuntimeError('Unpermitted dependency: ' + name)
    for label, args, expected in commands:
        old = checkpoint.get(label)
        module = label.removesuffix('-trust0')
        source = ROOT / (module + '.lean')
        compiled = output / (module + '.olean')
        log = OUT / (label + '.log')
        if (options.resume and old and expected is not None and source.exists() and compiled.exists() and log.exists()
                and old['source_sha256'] == digest(source) and old['olean_sha256'] == digest(compiled)
                and old['check']['sha256'] == digest(log) and old['check']['exit_code'] == 0):
            audit(label, log.read_text(encoding='utf-8'), expected)
            checks.append(old['check'])
            print('Resumed verified checkpoint ' + label, flush=True)
            continue
        print('Checking ' + label, flush=True)
        before = digest(source) if expected is not None else None
        result = subprocess.run([lake, *args], cwd=ROOT, encoding='utf-8',
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800)
        log.write_text(result.stdout, encoding='utf-8', newline='\n')
        if result.returncode:
            print(result.stdout[-12000:], flush=True)
            raise RuntimeError(label + ' failed: ' + str(result.returncode))
        if label == 'version' and 'Lean (version 4.34.0,' not in result.stdout:
            raise RuntimeError('Lean version mismatch')
        audit(label, result.stdout, expected)
        # Store portable command descriptions; no host-specific paths in public evidence.
        recorded_args = ['--dir', '../lean434', 'build'] if label == 'sibling-build' else args
        check = dict(command=['lake', *recorded_args], exit_code=0,
                     log=log.name, sha256=digest(log), verifier_sha256=digest(ROOT / 'verify.py'))
        checks.append(check)
        if expected is not None:
            if before != digest(source):
                raise RuntimeError('Source changed during checking: ' + module)
            checkpoint[label] = dict(source_sha256=before, olean_sha256=digest(compiled), check=check)
            checkpoint_path.write_text(json.dumps(checkpoint, indent=2), encoding='utf-8', newline='\n')
        print('Passed ' + label, flush=True)
    files = [item['module'] + '.lean' for item in modules] + [
        'modules.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'verify.py', 'verify_independent.py', 'README.md', 'INDEPENDENT.md', '.gitignore', 'verification/verify-initial.py']
    record = dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),
                  problem='JSP-000404 / Erdos 504',
                  scope='Exact alpha N=5*pi/7 for every 9<=N<=10; arbitrary-N classification not proved',
                  complete_original_problem=False, lean='4.34.0', dependencies=dependencies,
                  files={name: digest(ROOT / name) for name in files}, checks=checks,
                  environment='Windows; pinned dependency sources and compiled Mathlib caches',
                  network_isolated=False, independent_checker=False, official_review='pending',
                  priority='not asserted', solvers_in_verification_trust_chain=False,
                  record_scope='57 source modules checked individually with Lean kernel; separate Nanoda evidence')
    (OUT / 'result.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8', newline='\n')
    print('Verified all 57 modules; official review remains pending', flush=True)


if __name__ == '__main__':
    main()
