# JSP-001003: Monochromatic sum-product sets in 2-colorings

## Problem

Formalizes Schur triples, multiplicative Schur, van der Waerden numbers, and Hindman theorem properties.

## References

[Er80] Erdos (1980).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1003`

## Build

```bash
lake build Erdos1003
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
