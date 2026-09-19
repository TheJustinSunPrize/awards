"""Exact checks independent of Lean; no floating point or network access."""
from fractions import Fraction as Q
from itertools import product
from math import lcm
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def sums(n):
    values = {Q(0)}
    for d in range(1, n + 1):
        values |= {v + Q(1, d) for v in values}
    return values


def signed(m):
    values = {Q(0)}
    for d in range(1, m):
        values = {v + w * Q(1, d) for v in values for w in (-1, 0, 1)}
    return values


def obstruction(m):
    return {(Q(1, m) if m else Q(0)) - q for q in signed(m)}


def compatible(m, p):
    return all(q.numerator % p for q in obstruction(m))


def irreducible(m):
    return m > 0 and Q(0) not in obstruction(m)


def bound(m):
    return max(abs(q.numerator) for q in obstruction(m))


def bitset_count(n):
    scale = lcm(*range(1, n + 1))
    bits = 1
    for d in range(1, n + 1):
        bits |= bits << (scale // d)
    return bits.bit_count()


def expected_lean():
    return [[len(sums(n)) for n in range(11)],
            [irreducible(m) for m in range(10)],
            [bound(m) for m in range(8)],
            [[compatible(m, p) for p in PRIMES] for m in range(8)]]


def main():
    counts = [bitset_count(n) for n in range(17)]
    rational_counts = [len(sums(n)) for n in range(17)]
    assert counts == rational_counts
    for m in range(9):
        vals = sums(max(0, m - 1))
        assert signed(m) == {x - y for x, y in product(vals, repeat=2)}
    index_count = 0
    for m in range(1, 13):
        irr = irreducible(m)
        assert irr == (counts[m] == 2 * counts[m - 1])
        index_count += irr
        assert 2 ** index_count <= counts[m]
    extension_cases = 0
    for m in range(1, 9):
        for p in PRIMES:
            if irreducible(m) and p > bound(m):
                assert compatible(m, p)
            if not compatible(m, p):
                continue
            for k in range(3):
                n = m * p ** k
                if n <= 16:
                    assert counts[n] == 2 * counts[n - 1]
                    extension_cases += 1
    assert compatible(4, 2) and compatible(4, 23)
    assert not compatible(4, 3)
    assert counts[12] != 2 * counts[11]
    assert bound(4) == 25
    expected = expected_lean()
    output = ROOT / 'verification' / 'evaluation.log'
    if output.exists():
        actual = []
        remaining = output.read_text().strip()
        while remaining:
            item, end = json.JSONDecoder().raw_decode(remaining)
            actual.append(item)
            remaining = remaining[end:].strip()
        assert actual == expected, (actual, expected)
    print(json.dumps({'exact_counts_N_0_to_16': counts,
                      'independent_count_methods': ['rational set DP', 'integer LCM bitset'],
                      'signed_difference_checks_m_0_to_8': 9,
                      'doubling_equivalence_and_lower_bound_m_1_to_12': 12,
                      'compatible_extension_checks': extension_cases,
                      'lean_output_crosscheck': output.exists(),
                      'expected_lean_outputs': expected}, indent=2))


if __name__ == '__main__':
    main()
