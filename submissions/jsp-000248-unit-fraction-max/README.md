# JSP-000248: Largest denominator in unit fraction representation of 1

## Problem

Formalizes specific representations of 1 as sums of distinct unit fractions and verifies excluded denominators.

## References

[Ma00] Martin (2000).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos248`

## Build

```bash
lake build Erdos248
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
