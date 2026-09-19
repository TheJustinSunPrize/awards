# JSP-000912: What bounds hold for the sum of prescribed powers of consecutive divisor ratios minus one?

## Problem

This submission formalizes divisor sequences of specific integers, consecutive divisor ratios, and sum bounds for small cases.

## References

[Er80] Erdős, "A survey of problems in combinatorial number theory" — Ann. Discrete Math. (1980), 89-115.

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos912`

## Build

```bash
lake build Erdos912
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
