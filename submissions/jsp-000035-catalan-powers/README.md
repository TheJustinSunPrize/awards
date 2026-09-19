# JSP-000035: Catalan conjecture (consecutive perfect powers)

## Problem

Formalizes the key equation 3^2 - 2^3 = 1 and verifies no other small consecutive perfect powers exist.

## References

[Mi03] Mihailescu (2004).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos35`

## Build

```bash
lake build Erdos35
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
