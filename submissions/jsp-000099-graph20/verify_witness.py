"""Independent finite checks of the published Dyson–McKay witness.

These computations are evidence, not a Lean proof. No third-party packages.
graph6 specification: https://users.cecs.anu.edu.au/~bdm/data/formats.txt
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent


def decode_masks(record: bytes) -> list[int]:
    data = record.strip().removeprefix(b">>graph6<<")
    n = data[0] - 63
    assert 0 <= n <= 62, "Only small graph6 records are supported"
    assert len(data) == 1 + (n * (n - 1) // 2 + 5) // 6
    assert all(63 <= c <= 126 for c in data)
    bits = [((c - 63) >> shift) & 1 for c in data[1:] for shift in range(5, -1, -1)]
    assert not any(bits[n * (n - 1) // 2:]), "Nonzero padding"
    masks = [0] * n
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                masks[i] |= 1 << j
                masks[j] |= 1 << i
            p += 1
    return masks


def decode_matrix(record: bytes) -> list[list[int]]:
    """Second decoder using an indexed formula, not the first decoder's output."""
    data = record.strip().removeprefix(b">>graph6<<")
    n = data[0] - 63
    matrix = [[0 for _ in range(n)] for _ in range(n)]
    for a in range(n):
        for b in range(a + 1, n):
            position = b * (b - 1) // 2 + a
            chunk, offset = divmod(position, 6)
            matrix[a][b] = matrix[b][a] = ((data[chunk + 1] - 63) // (2 ** (5 - offset))) % 2
    return matrix


def enumerate_masks(masks: list[int]) -> dict:
    n = len(masks)
    counts = [0] * (n + 1)
    examples = {}
    checked = [0] * (n + 1)
    for subset in range(1, 1 << n):
        size = subset.bit_count()
        checked[size] += 1
        first = (subset & -subset).bit_length() - 1
        degree = (masks[first] & subset).bit_count()
        rest = subset & (subset - 1)
        regular = True
        while rest:
            bit = rest & -rest
            v = bit.bit_length() - 1
            if (masks[v] & subset).bit_count() != degree:
                regular = False
                break
            rest ^= bit
        if regular:
            counts[size] += 1
            examples.setdefault(str(size), {"vertices": [v for v in range(n) if subset >> v & 1], "degree": degree})
    return {"checked_by_size": checked, "regular_by_size": counts, "examples": examples,
            "maximum_regular_order": max(k for k, count in enumerate(counts) if count)}


def enumerate_matrix(matrix: list[list[int]], minimum: int) -> dict:
    """Enumerate tuple combinations and sum matrix rows; no bit-mask test."""
    n = len(matrix)
    checked = [0] * (n + 1)
    counts = [0] * (n + 1)
    for size in range(minimum, n + 1):
        for vertices in itertools.combinations(range(n), size):
            checked[size] += 1
            degree = sum(matrix[vertices[0]][u] for u in vertices)
            if all(sum(matrix[v][u] for u in vertices) == degree for v in vertices[1:]):
                counts[size] += 1
    return {"checked_by_size": checked, "regular_by_size": counts}


def controls() -> None:
    # Common degree zero must count, as must a larger-than-threshold cycle.
    assert enumerate_masks([0] * 6)["maximum_regular_order"] == 6
    assert enumerate_matrix([[0] * 6 for _ in range(6)], 6)["regular_by_size"][6] == 1
    complete = [[int(a != b) for b in range(6)] for a in range(6)]
    assert enumerate_matrix(complete, 6)["regular_by_size"][6] == 1
    cycle = [[int((a - b) % 7 in (1, 6)) for b in range(7)] for a in range(7)]
    result = enumerate_matrix(cycle, 6)["regular_by_size"]
    assert result[6] == 0 and result[7] == 1


def main() -> None:
    controls()
    data = (ROOT / "witness20.g6").read_bytes()
    masks, matrix = decode_masks(data), decode_matrix(data)
    assert len(masks) == 20
    assert all(matrix[a][b] == (masks[a] >> b & 1) for a in range(20) for b in range(20))
    start = time.monotonic()
    first = enumerate_masks(masks)
    bit_seconds = time.monotonic() - start
    start = time.monotonic()
    second = enumerate_matrix(matrix, 6)
    matrix_seconds = time.monotonic() - start
    assert first["maximum_regular_order"] == 5
    assert first["checked_by_size"][6:] == second["checked_by_size"][6:]
    assert first["regular_by_size"][6:] == second["regular_by_size"][6:] == [0] * 15
    result = {
        "meaning": "Finite computation only, not formal verification or a new mathematical result",
        "graph_sha256": hashlib.sha256(data).hexdigest(),
        "vertices": 20, "edges": sum(x.bit_count() for x in masks) // 2,
        "adjacency_masks": masks,
        "threshold": 6, "checked_at_or_above_threshold": sum(second["checked_by_size"]),
        "bit_mask_verifier": first, "matrix_verifier": second,
        "seconds": {"bit_mask": bit_seconds, "matrix": matrix_seconds},
        "negative_controls": "empty graph, complete graph, and C7 passed",
    }
    (ROOT / "verification-python.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
