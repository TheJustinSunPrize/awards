# JSP-000018: Moving sofa problem (maximum area)

## Problem

Formalizes bounds on the sofa area, properties of the corridor, and known sofa shapes (Gerver, Hammersley).

## References

[Ba24] Baek (2024); [Ge92] Gerver (1992).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos18`

## Build

```bash
lake build Erdos18
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
