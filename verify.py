#!/usr/bin/env python3
"""Cross-check the certificate independently, then invoke the pinned Lean kernel."""
import argparse
import hashlib
import math
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
BOUND = 12167


def factors(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def square(n):
    return math.isqrt(n) ** 2 == n


def powerful(n):
    return n > 0 and all(e >= 2 for e in factors(n).values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean', help='Path to Lean 4.19.0')
    args = parser.parse_args()
    source = (HERE / 'Proof.lean').read_bytes()
    text = source.decode('utf-8')
    blocks = re.findall(r'def witnesses(\d+) : List Nat := \[(.*?)\]', text, re.S)
    if [int(i) for i, _ in blocks] != list(range(122)):
        raise RuntimeError('Missing, duplicate, or reordered certificate blocks')
    witnesses = []
    for i, body in blocks:
        values = [int(x) for x in re.findall(r'\d+', body)]
        if len(values) != (66 if int(i) == 121 else 100):
            raise RuntimeError(f'Wrong length for certificate block {i}')
        witnesses.extend(values)
    for n, actual in enumerate(witnesses, 1):
        if square(n):
            expected = 4 * math.isqrt(n)
        elif square(n + 1):
            expected = 4 * math.isqrt(n + 1) + 1
        else:
            choices = [4*p + tag for m, tag in ((n, 2), (n+1, 3))
                       for p, e in factors(m).items() if e == 1]
            if not choices:
                raise RuntimeError(f'Unexpected smaller counterexample: {n}')
            expected = min(choices)
        if actual != expected:
            raise RuntimeError(f'Certificate mismatch at {n}: {actual} != {expected}')
    found = [n for n in range(1, BOUND+1)
             if powerful(n) and powerful(n+1) and not square(n) and not square(n+1)]
    if found != [BOUND]:
        raise RuntimeError(f'Independent enumeration disagrees: {found}')
    print('Proof.lean SHA-256:', hashlib.sha256(source).hexdigest(), flush=True)
    print('Independent trial-division check: PASS (12166 certificates; first pair 12167, 12168)', flush=True)
    print('Factorizations: 12167 = 23^3; 12168 = 2^3 * 3^2 * 13^2', flush=True)
    version = subprocess.run([args.lean, '--version'], check=True, capture_output=True,
                             text=True, encoding='utf-8').stdout.strip()
    if not re.search(r'Lean \(version 4\.19\.0,', version):
        raise RuntimeError('Expected pinned Lean 4.19.0; got ' + version)
    print(version, flush=True)
    result = subprocess.run([args.lean, '-s', '262144', 'Proof.lean'], cwd=HERE,
                            capture_output=True, text=True, encoding='utf-8', timeout=600)
    print(result.stdout, end='', flush=True)
    if result.stderr:
        print(result.stderr, end='', flush=True)
    if result.returncode:
        raise RuntimeError(f'Lean failed with exit code {result.returncode}')
    audits = re.findall(r"'JSP000301\.(\w+)' depends on axioms: \[([^]]*)\]", result.stdout)
    if {name for name, _ in audits} != {'prime_iff', 'negative_answer', 'smallest_counterexample'}:
        raise RuntimeError('Missing or unexpected axiom audit')
    if len(audits) != 3 or any(set(a.split(', ')) != {'propext', 'Quot.sound'} for _, a in audits):
        raise RuntimeError('Unexpected theorem dependencies')
    if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|decide\s+\+native', text):
        raise RuntimeError('Forbidden proof escape hatch in source')
    print('Lean kernel verification and axiom audit: PASS', flush=True)


if __name__ == '__main__':
    main()
