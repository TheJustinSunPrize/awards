#!/usr/bin/env python3
"""Independent integer enumeration. This is not the Lean proof."""
from itertools import combinations
from math import isqrt

WITNESS = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
           5, 25, 6, 16, 27, 32, 36, 48]
assert len(WITNESS) == len(set(WITNESS)) == 20
assert min(WITNESS) >= 1 and max(WITNESS) <= 48
products = {1}
for a in WITNESS:
    new = {a * p for p in products}
    assert not products.intersection(new)
    products.update(new)
assert len(products) == 2 ** 20
print('All 1,048,576 subset products are distinct.')

def distinct_sums(xs):
    sums = {0}
    for a in xs:
        new = {a + s for s in sums}
        if sums.intersection(new):
            return False
        sums.update(new)
    return True

def F(k):
    return max(r for r in range(k + 1)
               if any(distinct_sums(s) for s in combinations(range(1, k + 1), r)))

values = [F(k) for k in range(6)]
assert values == [0, 1, 2, 2, 3, 3]
primes = [p for p in range(2, 49)
          if all(p % d for d in range(2, isqrt(p) + 1))]
counts = [sum(p ** k <= 48 for p in primes) for k in [1, 2, 4]]
assert counts == [15, 3, 1]
assert sum(counts) == 19 < len(WITNESS)
print('F(0..5) =', values)
print('Exact-formula prediction at N=48: 15 + 3 + 1 = 19 < 20.')
