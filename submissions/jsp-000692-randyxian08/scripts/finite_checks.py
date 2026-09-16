#!/usr/bin/env python3
"""Independent finite regression checks. These are NOT Lean verification."""
from __future__ import annotations
from itertools import combinations
from math import comb
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def bit_indices(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def build_alon(r: int):
    if r < 2:
        raise ValueError("rank must be at least 2")
    core_size = 2 * r - 2
    core = (1 << core_size) - 1
    core_edges = {sum(1 << x for x in t) for t in combinations(range(core_size), r)}
    labels = [sum(1 << x for x in t) for t in combinations(range(core_size), r-1) if 0 in t]
    label_id = {a: core_size+i for i, a in enumerate(labels)}
    edges = set(core_edges)
    for a in labels:
        y = 1 << label_id[a]
        edges.add(a | y)
        edges.add((core ^ a) | y)
    return core_size, core, labels, label_id, core_edges, edges


def check_alon(r: int) -> dict:
    q, core, labels, label_id, core_edges, edges = build_alon(r)
    n = q + len(labels)
    expected_n = 2*r-2 + comb(2*r-2, r-1)//2
    assert n == expected_n
    assert all(e.bit_count() == r for e in edges)
    support = 0
    for e in edges:
        support |= e
    assert support == (1 << n)-1
    pair_count = 0
    for e, f in combinations(edges, 2):
        assert e & f
        pair_count += 1
    colours = [0]*(r-1) + [1]*(r-1) + [2]*len(labels)
    assert all(len({colours[v] for v in bit_indices(e)}) > 1 for e in edges)
    # Exhaust every CORE colouring, and check that its mathematical obstruction
    # is an actual constructed edge (or a pair forcing opposite label colours).
    for red in range(1 << q):
        blue = core ^ red
        if red.bit_count() >= r:
            a = sum(1 << v for v in list(bit_indices(red))[:r])
            assert a in core_edges
        elif blue.bit_count() >= r:
            a = sum(1 << v for v in list(bit_indices(blue))[:r])
            assert a in core_edges
        else:
            assert red.bit_count() == blue.bit_count() == r-1
            representative = red if red & 1 else blue
            label = 1 << label_id[representative]
            assert red | label in edges and blue | label in edges
    # The Fin m -> Bool injection in AlonGrowth: choose one point per pair,
    # always choosing the distinguished vertex 0 from the first pair.
    m = r-2
    selected = set()
    for b in range(1 << m):
        half = 1
        for i in range(m):
            half |= 1 << (2*(i+1) + ((b >> i) & 1))
        assert half.bit_count() == r-1 and half in label_id
        selected.add(half)
    assert len(selected) == 2**m
    assert n >= 2**m
    full_colouring_count = None
    if n <= 16:
        universe = (1 << n)-1
        for red in range(1 << n):
            blue = universe ^ red
            assert any(e & red == e or e & blue == e for e in edges)
        full_colouring_count = 1 << n
    return {
        "rank": r, "active_vertices": n, "edges": len(edges),
        "distinct_edge_pairs_checked": pair_count,
        "core_colourings_checked": 1 << q,
        "full_vertex_colourings_checked": full_colouring_count,
        "boolean_vectors_injected": 1 << m,
        "uniform": True, "intersecting": True, "no_isolated_vertices": True,
        "explicit_three_colouring": True, "core_two_colour_obstruction": True,
    }


def check_matrix(edges: set[int], name: str) -> dict:
    rank = next(iter(edges)).bit_count()
    universe = 0
    for e in edges:
        universe |= e
    s = max((e & f).bit_count() for e, f in combinations(edges, 2))
    tests = 0
    for e in edges:
        R = e
        for y in list(bit_indices(universe ^ R)):
            bigger = R | (1 << y)
            if all(f == e or (f & bigger) != f for f in edges):
                R = bigger
        assert e & R == e
        assert all(f == e or f & R != f for f in edges)
        Q = universe ^ R
        g = {}
        for x in bit_indices(e):
            choices = [f for f in edges if f & R == 1 << x]
            assert choices
            g[x] = choices[0]
        fy = {}
        for y in bit_indices(Q):
            choices = [f for f in edges if f != e and f & (R | 1 << y) == f]
            assert choices
            fy[y] = choices[0]
        for x0 in bit_indices(e):
            A = e ^ (1 << x0)
            B = g[x0] ^ (1 << x0)
            assert A.bit_count() == B.bit_count() == rank-1
            assert B & Q == B
            ones = zeros = 0
            for x in bit_indices(A):
                row = sum(bool(g[x] & (1 << y)) for y in bit_indices(B))
                assert row <= s
                ones += row
            for y in bit_indices(B):
                zero_rows = [x for x in bit_indices(A) if not g[x] & (1 << y)]
                assert all(fy[y] & (1 << x) for x in zero_rows)
                assert len(zero_rows) <= s
                zeros += len(zero_rows)
            assert ones + zeros == (rank-1)**2
            assert rank <= 2*s+1
            tests += 1
    return {"family": name, "rank": rank, "maximum_distinct_intersection": s,
            "matrix_checks": tests, "passed": True}


def main() -> None:
    families = [check_alon(r) for r in range(2, 8)]
    triples = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    fano = {sum(1 << v for v in e) for e in triples}
    matrix = [check_matrix(fano, "Fano")]
    matrix += [check_matrix(build_alon(r)[-1], f"Alon rank {r}") for r in range(2, 6)]
    for k in range(2049):
        assert (k+14)**3 <= 2**(k+12)
        assert (k+15)**3 <= 2*(k+14)**3
    report = {
        "status": "PASS", "evidence_type": "FINITE_REGRESSION_ONLY_NOT_A_LEAN_PROOF",
        "alon_checks": families, "matrix_checks": matrix,
        "total_matrix_checks": sum(x["matrix_checks"] for x in matrix),
        "growth_base_and_step_values_checked": 2049,
    }
    (ROOT / "verification").mkdir(exist_ok=True)
    (ROOT / "verification/finite-results.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
