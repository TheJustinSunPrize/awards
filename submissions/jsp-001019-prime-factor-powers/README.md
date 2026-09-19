# JSP-001019: If corresponding powers of two bases minus one always have identical prime-factor sets, must the bases be equal?

## Problem

This submission formalizes specific a^n - 1 values and their prime factorizations for bases 2 through 7, verifying that different bases produce different prime factor sets.

## References

[Er80] Erdős, "A survey of problems in combinatorial number theory" — Ann. Discrete Math. (1980), 89-115.

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1019`

## Build

```bash
lake build Erdos1019
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
