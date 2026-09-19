# JSP-001021: How large a transitive subtournament must every tournament of prescribed order contain?

## Problem

This submission formalizes the logarithmic lower bound for transitive subtournament sizes, verifies edge counts for tournaments, and checks the power-of-2 bounds.

## References

[ErMo64] Erdős & Moser (1964); [RePa70] Rédei & Pere (1970); [Sa94] Sánchez-Flores (1994).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1021`

## Build

```bash
lake build Erdos1021
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
