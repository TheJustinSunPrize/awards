"""Independent exact Gaussian-elimination cross-check of the degree criterion.

These finite tests do not substitute for the quantified Lean theorems.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from random import Random
import json
from magic_certificate import certificate, lines, parse_points


def gaussian(n, blocks):
    """Solve A w = 1 without the degree formula; return consistency, rank and unique solution."""
    rows = [[Q(a in l) for a in range(n)] + [Q(1)] for l in blocks]
    r = 0
    pivots = []
    for c in range(n):
        k = next((k for k in range(r, len(rows)) if rows[k][c]), None)
        if k is None:
            continue
        rows[r], rows[k] = rows[k], rows[r]
        t = rows[r][c]
        rows[r] = [x/t for x in rows[r]]
        for k in range(len(rows)):
            if k != r:
                t = rows[k][c]
                rows[k] = [x-t*y for x, y in zip(rows[k], rows[r])]
        pivots.append(c)
        r += 1
    consistent = all(any(row[:n]) or not row[n] for row in rows)
    if not consistent or r != n:
        return consistent, r, None
    sol = [Q(0)] * n
    for k, c in enumerate(pivots):
        sol[c] = rows[k][n]
    return True, r, sol


def check(points):
    c = certificate(points)
    n, blocks = len(points), lines(points)
    assert all(len(l) >= 2 for l in blocks)
    assert all(sum(a in l and b in l for l in blocks) == 1 for a, b in combinations(range(n), 2))
    consistent, rank, solution = gaussian(n, blocks)
    if c["mode"] == "degree-formula":
        assert rank == n, (points, rank)
        expected = consistent and all(w > 0 for w in solution)
        assert c["accepted"] == expected, (points, c, solution)
        if consistent:
            assert list(map(Q, c["candidate_weights"])) == solution
    else:
        assert consistent and c["accepted"]
    if c["accepted"]:
        weights = list(map(Q, c["candidate_weights"]))
        assert all(w > 0 for w in weights)
        assert all(sum((weights[a] for a in l), Q(0)) == 1 for l in blocks)
    return c


def main():
    grid = list(product(range(3), repeat=2))
    counts = {"accepted": 0, "rejected": 0}
    total = 0
    for mask in range(1 << len(grid)):
        points = [tuple(map(Q, p)) for a, p in enumerate(grid) if mask >> a & 1]
        c = check(points)
        counts["accepted" if c["accepted"] else "rejected"] += 1
        total += 1
    rng = Random(735)
    grid2 = list(product(range(5), repeat=2))
    for _ in range(400):
        points = [tuple(map(Q, p)) for p in rng.sample(grid2, rng.randrange(2, 17))]
        c = check(points)
        counts["accepted" if c["accepted"] else "rejected"] += 1
        total += 1
    named = {
        "failed-fano": [(0, 0), (6, 0), (0, 6), (3, 0), (0, 3), (3, 3), (2, 2)],
        "five-point-obstruction": [(0, 0), (1, 0), (2, 0), (0, 1), (1, 2)],
        "near-pencil": [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1)],
        "rational-triangle": [("1/3", "2/7"), ("2/5", "3/7"), ("4/5", "1/7")],
    }
    examples = {}
    for name, points in named.items():
        examples[name] = check(parse_points({"points": points}))
        total += 1
    assert examples["failed-fano"]["candidate_weights"] == ["1/4"] * 3 + ["1/2"] * 3 + ["1/4"]
    assert examples["failed-fano"]["accepted"]
    assert not examples["five-point-obstruction"]["accepted"]
    assert examples["near-pencil"]["accepted"] and examples["rational-triangle"]["accepted"]
    assert not examples["five-point-obstruction"]["nonpositive_points"]  # positivity alone is insufficient
    try:
        certificate([(Q(0), Q(0)), (Q(0), Q(0))])
        raise AssertionError("Duplicate points were accepted")
    except ValueError:
        pass
    try:
        parse_points({"points": [[0.1, 0]]})
        raise AssertionError("Inexact coordinates were accepted")
    except ValueError:
        pass
    print(json.dumps({"tests": total, "exhaustive_3x3_subsets": 512,
                      "random_5x5_subsets": 400, "random_seed": 735,
                      "grid_counts": counts, "named": examples,
                      "method": "Exact Fraction Gaussian elimination independent of the degree formula"}, indent=2))


if __name__ == "__main__":
    main()
