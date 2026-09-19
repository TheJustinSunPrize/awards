# JSP-000205: Maximum density of distance-1 avoiding sets

## Problem

Formalizes bounds on density of measurable sets avoiding distance 1, Moser spindle, and chromatic number bounds.

## References

[Ta24] Tao (2024).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos205`

## Build

```bash
lake build Erdos205
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
