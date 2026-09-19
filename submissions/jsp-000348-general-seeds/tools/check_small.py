"""Finite definition checks only; the infinite conclusions are proved in Lean."""
from itertools import product
import json


def extend(seed, length=40):
    a = list(seed)
    while len(a) < length:
        # Independent definitions: direct block enumeration and prefix differences.
        direct = {sum(a[p:q]) for p in range(len(a)) for q in range(p + 2, len(a) + 1)}
        prefix = [0]
        for x in a:
            prefix.append(prefix[-1] + x)
        differences = {prefix[q] - prefix[p] for p in range(len(a))
                       for q in range(p + 2, len(a) + 1)}
        assert direct == differences
        candidates = [v for v in direct if v > a[-1]]
        assert candidates
        a.append(min(candidates))
    assert a[:len(seed)] == list(seed)
    assert all(a[i] < a[i + 1] for i in range(len(seed) - 1, len(a) - 1))
    assert all(a[i] - i <= a[i + 1] - (i + 1)
               for i in range(len(seed) - 1, len(a) - 1))
    return a


def main():
    count = 0
    for length in range(2, 5):
        for seed in product(range(1, 5), repeat=length):
            extend(seed)
            count += 1
    classical = extend((1, 2))
    assert classical[:20] == [1, 2, 3, 5, 6, 8, 10, 11, 14, 16,
                              17, 18, 19, 21, 22, 24, 25, 29, 30, 32]
    print(json.dumps({"positive_seeds_checked": count, "terms_per_seed": 40,
                      "unsorted_example": extend((9, 1))[:12],
                      "repeated_example": extend((2, 2))[:12],
                      "classical_first_20": classical[:20],
                      "scope": "Finite checks of definitions, not evidence of the asymptotic theorem."},
                     indent=2))


if __name__ == "__main__":
    main()
