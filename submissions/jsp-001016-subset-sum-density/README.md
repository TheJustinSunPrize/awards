# JSP-001016: In every partition of the natural numbers into two parts, must one part's finite subset sums have a uniform positive lower logarithmic density?

## Problem

This submission formalizes properties of logarithmic density, specific partition examples, and subset sum properties for small sets.

## References

[Er80] Erdős, "A survey of problems in combinatorial number theory" — Ann. Discrete Math. (1980), 89-115.

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1016`

## Build

```bash
lake build Erdos1016
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
