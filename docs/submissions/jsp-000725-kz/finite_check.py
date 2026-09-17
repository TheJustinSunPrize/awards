"""Independent finite diagnostic; the universal result is proved in Lean."""
from math import isqrt

checked = 0
for n in range(41):
    m = isqrt(4*n + 1) - 1
    a = list(range(n-m+1, n+1))
    sums = {0: {0}}
    for x in a:
        updated = {s: set(counts) for s, counts in sums.items()}
        for s, counts in sums.items():
            updated.setdefault(s+x, set()).update(c+1 for c in counts)
        sums = updated
    assert all(len(counts) == 1 for counts in sums.values()), n
    assert len(a) == m and all(1 <= x <= n for x in a), n
    checked += 1
for t in range(2, 31):
    n = t*t+t-1
    a = set(range(t*t-t, n+1))
    s = set(range(t*t+1, t*t+t))
    u = set(range(t*t-t, t*t))
    assert s <= a and u <= a and len(a) == 2*t
    assert sum(s) == sum(u) and len(s) == t-1 and len(u) == t
print(f'PASS: every subset-sum cardinality for N=0,...,40 ({checked} intervals)')
print('PASS: boundary witnesses for t=2,...,30 (29 intervals)')
print('Finite diagnostic only; no claim of universal proof from enumeration')
