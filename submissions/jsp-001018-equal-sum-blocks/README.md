# JSP-001018: Must every sufficiently long integer sequence with bounded gaps have two distinct consecutive blocks with equal sums?

## Problem

This submission formalizes specific sequences with equal-sum consecutive blocks, verifies the pigeonhole principle for bounded sequences, and checks small case verifications.

## References

[Er80] Erdős, "A survey of problems in combinatorial number theory" — Ann. Discrete Math. (1980), 89-115.

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1018`

## Build

```bash
lake build Erdos1018
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
