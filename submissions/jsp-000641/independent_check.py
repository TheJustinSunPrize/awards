#!/usr/bin/env python3
"""Independent forward DP check; not used as an oracle by the Lean proof."""
from pathlib import Path
from itertools import groupby
import json

root = Path(__file__).resolve().parent
witness = json.loads((root / 'coloring.json').read_text())
bits, n, k = witness['color_bits'], witness['n'], witness['k']
assert len(bits) == n and set(bits) <= {'0', '1'}
assert n == k*k-k+1
lengths, paths = {}, {}
for b in range(1, n+1):
    for a in range(1, b):
        if bits[a-1] != bits[b-1]:
            continue
        predecessors = [(z, a) for z in range(1, a)
                        if a-z >= b-a and bits[z-1] == bits[a-1]]
        best = max(predecessors, key=lengths.get, default=None)
        lengths[a, b] = 2 if best is None else lengths[best]+1
        paths[a, b] = [a, b] if best is None else paths[best]+[b]
max_pair = max(lengths, key=lengths.get)
max_length = lengths[max_pair]
assert max_length == 11 and max_length < k
print(json.dumps({'n':n, 'k':k, 'quadratic_prediction':n,
                  'maximum_monochromatic_descending_wave_length':max_length,
                  'example_longest_wave':paths[max_pair],
                  'alternating_block_lengths':[len(list(g)) for _, g in groupby(bits)],
                  'passed':True,
                  'scope':'Independent finite check; Lean establishes the universal no-wave statement.'}, indent=2))
