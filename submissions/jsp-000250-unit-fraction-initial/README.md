# JSP-000250: Initial denominators in unit fraction representations of 1

## Problem

Formalizes representations of 1 with bounded denominators and Sylvester sequence properties.

## References

[LiSa24] Lichtman & Sanna (2024).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos250`

## Build

```bash
lake build Erdos250
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
