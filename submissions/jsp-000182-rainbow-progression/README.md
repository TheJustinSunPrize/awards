# JSP-000182: Monochromatic or rainbow arithmetic progression

## Problem

Formalizes van der Waerden numbers, Schur numbers, and specific 3-term APs.

## References

[Er79] Erdos et al. (1979).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos182`

## Build

```bash
lake build Erdos182
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
