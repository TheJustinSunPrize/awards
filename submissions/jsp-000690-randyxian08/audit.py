"""Independent finite audit of Li's arXiv:2512.24850 witness.
This script is NOT a Lean proof. Vertices retain the paper's labels 1,...,9.
"""
from itertools import product
import json
from pathlib import Path
from source_audit import audit_source

EDGES = [
    (1,2,3),(1,2,9),(1,3,8),(1,4,6),(1,4,8),(1,4,9),
    (1,5,7),(1,5,8),(1,5,9),(1,6,7),(2,3,6),(2,3,7),
    (2,4,9),(2,5,9),(2,6,7),(3,4,8),(3,5,8),(3,6,7),
    (4,6,8),(4,6,9),(5,7,8),(5,7,9)
]
EDGE_BLUE = [
    (6,7,8,9),(3,4,5,6),(2,4,5,6),(2,7,8,9),(3,5,6,9),
    (2,5,6,8),(2,6,8,9),(3,4,7,9),(2,4,7,8),(2,3,4,5),
    (1,7,8,9),(1,6,8,9),(1,3,5,6),(1,3,4,7),(1,3,4,5),
    (1,2,5,6),(1,2,4,7),(1,2,4,5),(1,3,7,9),(1,2,7,8),
    (1,3,6,9),(1,2,6,8)
]
VERTEX_BLUE = [
    (2,3,4,5),(1,3,4,5),(1,2,4,5),(1,2,5,6),(1,2,4,7),
    (1,2,4,5),(1,2,4,5),(1,2,4,7),(1,2,6,8)
]
THREE = {1:0,2:0,3:1,4:0,5:0,6:1,7:2,8:1,9:1}

def proper(edges, coloring):
    return all(len({coloring[v] for v in edge}) > 1 for edge in edges)

def audit():
    if not __debug__:
        raise RuntimeError("Do not run this assertion-based audit with python -O")
    source_result = audit_source(Path(__file__).with_name('JSP690.lean'), {
        'edges': EDGES, 'edge_blue': EDGE_BLUE,
        'vertex_blue': VERTEX_BLUE, 'three': THREE,
    })
    assert len(set(EDGES)) == len(EDGES) == 22
    assert all(len(set(e)) == 3 and tuple(sorted(e)) == e
               and all(1 <= v <= 9 for v in e) for e in EDGES)
    degrees = [sum(v in e for e in EDGES) for v in range(1,10)]
    assert degrees == [10,7,7,7,7,7,7,7,7]
    colorings = [dict(zip(range(1,10),c)) for c in product((0,1),repeat=9)]
    binary_count = sum(proper(EDGES,c) for c in colorings)
    assert binary_count == 0
    assert proper(EDGES,THREE)
    assert len(EDGE_BLUE) == len(EDGES)
    for i, blue in enumerate(EDGE_BLUE):
        c = {v:int(v in blue) for v in range(1,10)}
        mono = [j for j,e in enumerate(EDGES) if not proper([e],c)]
        assert mono == [i], (i,mono)
    for v, blue in enumerate(VERTEX_BLUE,1):
        c = {w:int(w in blue) for w in range(1,10)}
        assert proper([e for e in EDGES if v not in e],c),v
    # A proper coloring of every strict edge subfamily is certified by choosing
    # any missing edge and restricting its deletion coloring. No enumeration
    # of all 2^22 subfamilies is needed for this implication.
    return {
        "source":"https://arxiv.org/abs/2512.24850v1",
        "source_consistency_audit":source_result,
        "vertex_labels":list(range(1,10)),"edges":EDGES,
        "degrees":degrees,"minimum_degree":min(degrees),
        "binary_colorings_checked":len(colorings),
        "proper_binary_colorings":binary_count,
        "three_coloring":THREE,"edge_deletion_blue_sets":EDGE_BLUE,
        "vertex_deletion_blue_sets":VERTEX_BLUE,
        "edge_deletion_certificates_checked":22,
        "vertex_deletion_certificates_checked":9,
        "status":"all independent Python assertions passed",
        "lean_verification":"This audit does not establish Lean verification."
    }

if __name__ == '__main__':
    result=audit()
    print(json.dumps(result,indent=2))
    Path(__file__).with_name('audit-results.json').write_text(
        json.dumps(result,indent=2)+'\n',encoding='utf-8')
