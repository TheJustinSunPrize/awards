"""Exact rational-coordinate convenience checker; the Python implementation is not formalized.

Usage: python3 tools/magic_certificate.py points.json
Input: {"points": [[0, 0], ["1/2", 1], ...]}. Floats and duplicate points are rejected.
The Lean accepts_iff theorem certifies its mathematical incidence criterion.
"""
from fractions import Fraction as Q
from itertools import combinations
import json
import sys


def lines(points):
    """Compute maximal collinear subsets using exact 2-by-2 determinants."""
    out = set()
    for a, b in combinations(range(len(points)), 2):
        x, y = points[a]
        u, v = points[b]
        out.add(tuple(c for c, (s, t) in enumerate(points)
                      if (u-x)*(t-y) == (v-y)*(s-x)))
    return sorted(out)


def certificate(points):
    if len(set(points)) != len(points):
        raise ValueError("Points must be distinct")
    n = len(points)
    blocks = lines(points)
    degrees = [sum(a in l for l in blocks) for a in range(n)]
    if n <= 1:
        weights = [Q(1)] * n
        mode = "empty-or-singleton"
        R = Y = None
    elif len(blocks) == 1:
        weights = [Q(1, n)] * n
        mode = "collinear"
        R = Y = None
    else:
        assert all(k > 1 for k in degrees)
        R = sum((Q(1, k-1) for k in degrees), Q(0))
        Y = (n + R) / (1 + R)
        weights = [(k-Y)/(k-1) for k in degrees]
        mode = "degree-formula"
    bad_points = [a for a, w in enumerate(weights) if w <= 0]
    bad_lines = [dict(line=list(l), total=str(sum((weights[a] for a in l), Q(0))))
                 for l in blocks if sum((weights[a] for a in l), Q(0)) != 1]
    return dict(accepted=not bad_points and not bad_lines, mode=mode,
                point_count=n, lines=[list(l) for l in blocks], degrees=degrees,
                reciprocal_sum=None if R is None else str(R),
                forced_total=None if Y is None else str(Y),
                candidate_weights=[str(w) for w in weights],
                nonpositive_points=bad_points, failed_line_sums=bad_lines)


def parse_points(obj):
    points = obj["points"]
    if any(len(p) != 2 or any(type(x) not in (int, str) for x in p) for p in points):
        raise ValueError("Each point must contain two integers or rational strings; no floats")
    return [tuple(Q(x) for x in p) for p in points]


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        points = parse_points(json.load(f))
    print(json.dumps(certificate(points), indent=2))
