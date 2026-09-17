"""Rebuild the partial planar formalization and audit its final dependency closures."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
MODULES = ['SendovFiveDirections', 'SendovDirectionGeometry', 'SendovFivePointPlane', 'FivePointExact', 'SendovDirectionModel', 'SendovSixDirections', 'SendovSixPointPlane', 'SmallCasesExact', 'SendovStrictPower', 'PowerCasesExact', 'VerifiedCasesExact']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    OUT.mkdir(exist_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Install the pinned Lean toolchain and put lake on PATH')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    dependencies = {}
    for package in manifest['packages']:
        directory = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory,
                                          text=True).strip()
        if revision != package['rev']:
            raise RuntimeError('Dependency revision mismatch: ' + package['name'])
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                        cwd=directory, text=True).strip()
        if dirty:
            raise RuntimeError('Tracked dependency changes: ' + package['name'])
        dependencies[package['name']] = revision
    expected = {}
    for module in MODULES:
        source = (ROOT / (module + '.lean')).read_text(encoding='utf-8')
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', source):
            raise RuntimeError('Unexpected source construct: ' + module)
        expected[module] = {('JSP404' if module in ['FivePointExact', 'SmallCasesExact', 'PowerCasesExact', 'VerifiedCasesExact'] else module) + '.' + n for n in re.findall(r'^#print axioms (\w+)', source, re.M)}
        if not expected[module]:
            raise RuntimeError('Missing audit declarations: ' + module)
    commands = [('version', ['env', 'lean', '--version'], None),
                ('build', ['build'], None)]
    commands += [(m + '-trust0', ['env', 'lean', '--trust=0', m + '.lean'], expected[m])
                 for m in MODULES]
    checks = []
    for label, args, required in commands:
        result = subprocess.run([lake, *args], cwd=ROOT, encoding='utf-8',
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
        log = OUT / (label + '.log')
        log.write_text(result.stdout, encoding='utf-8', newline='\n')
        print(result.stdout, end='', flush=True)
        if result.returncode:
            raise RuntimeError(label + ' failed')
        if label == 'version' and 'Lean (version 4.34.0,' not in result.stdout:
            raise RuntimeError('Lean version mismatch')
        if required is not None:
            audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
            if {name for name, _ in audits} != required:
                raise RuntimeError('Audit coverage mismatch: ' + label)
            for name, axioms in audits:
                if {a.strip() for a in axioms.split(',') if a.strip()} - ALLOWED:
                    raise RuntimeError('Unexpected axiom dependency: ' + name)
        checks.append({'command': ['lake', *args], 'exit_code': 0,
                       'log': log.name, 'sha256': digest(log)})
    sources = [m + '.lean' for m in MODULES] + [
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'verify.py',
        'generate_five_direction_proof.py', 'generate_six_direction_proof.py', 'SendovFiveDirections.generation.json', 'SendovSixDirections.generation.json', 'README.md',
        'verify_independent.py', 'INDEPENDENT.md']
    record = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'problem': 'JSP-000404 / Erdos 504',
        'scope': 'Exact small cases N=5..8 and alpha(2^n)=(1-1/n)*pi for every n>=2; general classification remains unproved',
        'complete_original_problem': False,
        'lean': '4.34.0', 'dependencies': dependencies,
        'files': {name: digest(ROOT / name) for name in sources}, 'checks': checks,
        'environment': 'Windows; pinned dependency checkouts and compiled Mathlib caches',
        'network_isolated': False, 'independent_checker': False,
        'record_scope': 'Lean build/kernel checks; separate external evidence is in independent-result.json',
        'official_review': 'pending', 'priority': 'not asserted',
        'z3_in_verification_trust_chain': False,
    }
    (OUT / 'result.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
