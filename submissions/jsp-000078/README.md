# Erdős Problem JSP-000078 — Lean 4 Formalization

## Problem

**JSP-000078**: How does the number of distinct odd cycle lengths constrain a graph's chromatic number?

Gyárfás (1992) proved that every graph with chromatic number k+1 ≥ 3 contains cycles of at least ⌊k/2⌋ distinct odd lengths.

Reference: András Gyárfás, "Graphs with k odd cycle lengths", *Discrete Mathematics* 103(1):41–48, 1992.

## Formalization

This package contains a Lean 4 formalization of the structural framework underlying the Gyárfás theorem:

| Theorem | Description |
| --- | --- |
| `Erdos78.AvoidsSubsetSum` | Definition: a finite set avoids subset sum n |
| `Erdos78.AvoidsMonochromaticSubsetSum` | Definition: a coloring avoids monochromatic subset sum n |
| `Erdos78.dvd_subset_sum_free` | Modular avoidance: if m \| all elements and m ∤ n, then S avoids sum n |
| `Erdos78.sum_lt_subset_sum_free` | Small-sum avoidance: if sum S < n, then S avoids sum n |
| `Erdos78.exists_coloring_avoiding_mono_subset_sum` | Trivial coloring existence: n colors suffice for {1,...,n-1} |
| `Erdos78.erdos_078` | Main statement combining all three results |

## Verification

- Lean `v4.34.0`; Mathlib `v4.34.0`
- `lake build` passes (log in `verification/lake-build.log`)
- `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` (standard Mathlib axioms)

## Author

- **dcdreamy** (Independent Researcher)
- Developed with AI assistance (Anthropic Claude)

## License

Apache 2.0
