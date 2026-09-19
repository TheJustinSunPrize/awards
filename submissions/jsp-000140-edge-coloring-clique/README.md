# JSP-000140: How many edge colors are necessary if every four-vertex clique must contain at least five colors?

## Problem

This submission formalizes edge counts of complete graphs, K_4 subgraph counting, and the asymptotic bound f(n,4,5) = 5n/6 for small n values.

## References

[BCDP22] arXiv:2207.02920 (2022); [JoMu22] arXiv:2208.12563 (2022).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos140`

## Build

```bash
lake build Erdos140
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
