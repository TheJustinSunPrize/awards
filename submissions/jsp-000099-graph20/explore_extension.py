"""Bounded search: can THIS 20-vertex witness be extended by one vertex?

For each old subset S of size >=5, a regular extension must have common
degree d, with x_v=d-deg_S(v) in {0,1}, and sum(x_v)=d. Such an assignment
on S is forbidden. Mark every 20-bit neighborhood matching any pattern.
No claim about all 21-vertex graphs follows from failure to extend one graph.
"""
from pathlib import Path
import json
import time
from verify_witness import decode_masks, enumerate_masks

ROOT = Path(__file__).resolve().parent


def main():
    start = time.monotonic()
    adjacency = decode_masks((ROOT / "witness20.g6").read_bytes())
    n = len(adjacency)
    full = (1 << n) - 1
    patterns = []
    for subset in range(1 << n):
        if subset.bit_count() < 5:
            continue
        degrees = []
        bits = subset
        low, high = n, 0
        while bits:
            bit = bits & -bits
            v = bit.bit_length() - 1
            d = (adjacency[v] & subset).bit_count()
            degrees.append((bit, d))
            low, high = min(low, d), max(high, d)
            if high - low > 1:
                break
            bits ^= bit
        if high - low > 1:
            continue
        for d in range(high, low + 2):
            required = sum(bit for bit, old_degree in degrees if old_degree < d)
            if required.bit_count() == d:
                patterns.append((subset, required, d))
    patterns.sort(key=lambda item: (item[0].bit_count(), item[0], item[1]))
    covered = bytearray(1 << n)
    count = 0
    used = 0
    for subset, required, _ in patterns:
        free = full ^ subset
        assignment = free
        while True:
            value = required | assignment
            if not covered[value]:
                covered[value] = 1
                count += 1
            if assignment == 0:
                break
            assignment = (assignment - 1) & free
        used += 1
        if count == 1 << n:
            break
    allowed = [x for x, value in enumerate(covered) if not value]
    result = {
        "scope": "Extensions of this one fixed graph only; not all graphs of order 21",
        "neighborhoods": 1 << n,
        "forbidden_patterns": len(patterns),
        "patterns_needed_to_cover": used,
        "excluded_neighborhoods": count,
        "surviving_neighborhoods": len(allowed),
        "seconds": time.monotonic() - start,
        "formal_status": "Computational exploration, not Lean verified",
    }
    if allowed:
        x = allowed[0]
        extended = [a | (((x >> v) & 1) << n) for v, a in enumerate(adjacency)] + [x]
        check = enumerate_masks(extended)
        assert check["maximum_regular_order"] == 5
        result["first_survivor"] = {"adjacency_masks": extended, "exhaustive_check": check}
    (ROOT / "extension-exploration.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
