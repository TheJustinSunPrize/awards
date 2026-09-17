"""Exhaustive corroboration, not a replacement for the universal Lean proof."""
import json
from math import isqrt


def avoids_adjacent(B):
    xs = sorted(B)
    return all(x * y not in B for x, y in zip(xs, xs[1:]))


def distinct_blocks(B):
    products = set()
    xs = sorted(B)
    for i in range(len(xs)):
        value = 1
        for j in range(i, len(xs)):
            value *= xs[j]
            if value in products:
                return False
            products.add(value)
    return True


def main():
    records = []
    for N in range(19):
        qualifying = 0
        minimum = N
        for mask in range(1 << N):
            B = {i + 1 for i in range(N) if mask & (1 << i)}
            if not avoids_adjacent(B):
                continue
            qualifying += 1
            E = N - len(B)
            minimum = min(minimum, E)
            assert isqrt(N) <= E + isqrt(isqrt(N)) + 1, (N, B)
            for m in range(isqrt(N) + 1):
                assert m <= E + isqrt(m) + 1, (N, m, B)
        records.append({"N": N, "qualifying_sets": qualifying,
                        "minimum_deficit": minimum})
    B = set(range(1, 17))
    assert not avoids_adjacent(B)
    assert isqrt(16) > isqrt(isqrt(16)) + 1
    # Adjacent-product avoidance is strictly weaker than the original property.
    B = {2, 3, 4, 5, 24}
    assert avoids_adjacent(B) and not distinct_blocks(B)
    assert distinct_blocks({2, 3, 5, 7, 11})
    print(json.dumps({"cutoffs": records, "total_sets_enumerated": 2 ** 19 - 1,
                      "boundary_controls": 3}, indent=2))


if __name__ == "__main__":
    main()
