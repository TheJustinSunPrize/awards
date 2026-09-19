#!/usr/bin/env python3
"""Independent exhaustive feasibility check; not part of Lean's trusted proof.

Construction: Ruiliang Li, arXiv:2512.24850v1, Appendix A.
This implementation was written independently of the paper's script.
"""
import itertools
import json
from pathlib import Path
import re

edges = [
    (1, 2, 3), (1, 2, 9), (1, 3, 8), (1, 4, 6), (1, 4, 8), (1, 4, 9),
    (1, 5, 7), (1, 5, 8), (1, 5, 9), (1, 6, 7), (2, 3, 6), (2, 3, 7),
    (2, 4, 9), (2, 5, 9), (2, 6, 7), (3, 4, 8), (3, 5, 8), (3, 6, 7),
    (4, 6, 8), (4, 6, 9), (5, 7, 8), (5, 7, 9),
]
source = (Path(__file__).resolve().parent / "Main.lean").read_text(encoding="utf-8")
block = source.split("def exampleGraph : Hypergraph 9 :=", 1)[1].split("theorem uniform", 1)[0]
lean_edges = [tuple(int(x) + 1 for x in triple)
              for triple in re.findall(r"\((\d+),\s*(\d+),\s*(\d+)\)", block)]
assert lean_edges == edges, "Lean edge transcription differs from the paper data"
assert len(edges) == len(set(edges)) == 22
assert all(len(set(e)) == 3 for e in edges)
degrees = [sum(v in e for e in edges) for v in range(1, 10)]
assert degrees == [10] + [7] * 8
edge_masks = [sum(1 << (v - 1) for v in e) for e in edges]


def monochromatic(edge, blue):
    return blue & edge in (0, edge)


violations = {blue: [i for i, mask in enumerate(edge_masks) if monochromatic(mask, blue)]
              for blue in range(512)}
assert all(violations.values()), "Unexpected proper binary colouring"
edge_witnesses = [next(b for b, bad in violations.items() if bad == [i]) for i in range(22)]
vertex_witnesses = [next(b for b in range(512)
                        if all(v in e or not monochromatic(edge_masks[i], b)
                               for i, e in enumerate(edges))) for v in range(1, 10)]
three = next(cs for cs in itertools.product(range(3), repeat=9)
             if all(len({cs[v - 1] for v in e}) > 1 for e in edges))
print(json.dumps({"degrees": degrees, "binary_colourings_checked": 512,
                  "proper_binary_colourings": 0, "edge_deletion_masks": edge_witnesses,
                  "vertex_deletion_masks": vertex_witnesses,
                  "proper_three_colouring": three}, indent=2))
print("PASS: data transcription, degrees, non-colourability, and all deletion witnesses.")
