#!/usr/bin/env python3
"""Replay every project mathematical module, using the same Lean kernel.

ReplayBatch.lean is reused unchanged and attributed to the authors recorded in
NOTICE and REFERENCES.md. Mathlib and its dependencies remain trusted imports.
"""
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'verification/upstream-manifest.json').read_text())
    modules = sorted(item['module'] for item in manifest['files']) + [
        'FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference',
        'JSP000078.Compactness',
        'JSP000078.GeneralGraph',
        'JSP000078',
    ]
    if len(modules) != len(set(modules)) or len(modules) != 39:
        raise RuntimeError('Unexpected mathematical module closure')
    command = ['lake', 'env', 'lean', '--run', 'ReplayBatch.lean', *modules]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    log = ROOT / 'verification/replay.actual.log'
    log.write_text(result.stdout)
    print(result.stdout, end='')
    result.check_returncode()
    matches = re.findall(r'^Successfully replayed (\d+) declarations from (\d+) modules\.$',
                         result.stdout, re.M)
    if len(matches) != 1 or int(matches[0][1]) != len(modules):
        raise RuntimeError('Missing or inconsistent successful replay summary')
    collected = re.findall(r'^Collected (\S+)$', result.stdout, re.M)
    if collected != modules:
        raise RuntimeError('Replay did not collect the exact expected modules')
    record = {'exit_code': result.returncode, 'command': command, 'modules': modules,
              'declaration_count': int(matches[0][0]), 'module_count': len(modules),
              'scope': 'Same Lean kernel; project declarations replayed against Mathlib imports. '
                       'Not an independent implementation or fresh replay of Mathlib.'}
    (ROOT / 'verification/replay.actual.json').write_text(json.dumps(record, indent=2) + '\n')


if __name__ == '__main__':
    main()
