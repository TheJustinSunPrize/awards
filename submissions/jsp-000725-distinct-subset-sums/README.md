# JSP-000725: How large can an integer-interval subset be if subset sums using different numbers of terms are never equal?

## Problem

This submission formalizes specific subsets with distinct cross-cardinality subset sums, verifies the powers-of-2 construction, and checks the Sidon-like property.

## References

[Er80] Erdős, "A survey of problems in combinatorial number theory" — Ann. Discrete Math. (1980), 89-115.

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos725`

## Build

```bash
lake build Erdos725
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
