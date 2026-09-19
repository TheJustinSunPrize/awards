# JSP-001022: Divisibility chains in positive-density integer sets

## Problem

Formalizes divisibility chains, logarithmic density, primitive sets, and the Davenport-Erdos theorem.

## References

[ABLLPSTT26] Alexeev et al. (2026).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1022`

## Build

```bash
lake build Erdos1022
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
