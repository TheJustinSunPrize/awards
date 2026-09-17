#!/usr/bin/env python3
"""Exact experiments for the new product proof; NOT a Lean or universal proof check."""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O / PYTHONOPTIMIZE: integer checks use assertions')


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def check_pair(k: int, p: int) -> dict:
    if not (k >= 9 and prime(p) and k < 2*p and 3*p + 2 <= 2*k):
        raise ValueError('FiniteConstructionClaim hypotheses are not satisfied')
    L = math.lcm(*range(1, k))
    M = L // p
    m = k * M
    J = [j for j in range(1, k) if j != p]
    P = math.prod(J)
    assert p*M == L and P % M == 0 and math.gcd(p, M) == 1
    assert all(M % j == 0 for j in J)
    assert M >= 2 and m >= 2*k and m % p != 0
    r = m % p
    right = r > k-p-1
    n = m+k-1 if right else m
    i0 = k-1 if right else 0
    term = lambda j: m+j if right else m-j
    q = {j: k*(M//j) + (1 if right else -1) for j in J}
    a, b = (p-r, 2*p-r) if right else (r, r+p)
    assert a in J and b in J and a != b
    assert term(a) % p == 0 and term(b) % p == 0
    assert q[a] % p == 0 and q[b] % p == 0
    assert all(term(j) == j*q[j] and math.gcd(k, q[j]) == 1 for j in J)
    assert math.gcd(k, term(p)) == 1
    Q = math.prod(q.values())
    B = math.comb(n if right else m-1, k-1)
    C = math.comb(n, k)
    assert C == M*B and p*B == term(p)*Q
    assert B % term(p) == 0
    # The erased product still contains p, for EVERY indexed denominator factor.
    for j in J:
        erased = Q // q[j]
        assert erased % p == 0
        assert B % q[j] == 0
    failures = [i for i in range(k) if C % (n-i)]
    assert failures == [i0] and n-i0 == m
    assert C % m != 0 and n <= 3*L
    return {'k': k, 'p': p, 'right': right, 'a': a, 'b': b,
            'offset': i0, 'center_bits': m.bit_length(), 'binomial_bits': C.bit_length(),
            'passed': True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=300)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'evidence',
                        help='Separate output directory for this run')
    args = parser.parse_args()
    if args.max_k < 9:
        raise SystemExit('--max-k must be at least 9')
    start = time.monotonic()
    rows, skipped = [], []
    for k in range(9, args.max_k + 1):
        ps = [p for p in range(k//2+1, (2*k-2)//3+1) if prime(p)]
        if not ps:
            skipped.append(k)
        for p in ps:
            rows.append(check_pair(k, p))
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    with (out / 'product-cases.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=['k','p','right','a','b','offset','center_bits','binomial_bits','passed'])
        writer.writeheader(); writer.writerows(rows)
    summary = {'status': 'finite_experiments_only_not_a_formal_proof',
               'max_k': args.max_k, 'pairs_checked': len(rows),
               'k_values_checked': len({r['k'] for r in rows}), 'skipped_k': skipped,
               'failures': 0, 'right_cases': sum(r['right'] for r in rows),
               'elapsed_seconds': time.monotonic()-start}
    (out/'product-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
