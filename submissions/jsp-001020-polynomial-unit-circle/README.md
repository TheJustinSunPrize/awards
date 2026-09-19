# JSP-001020: Bounded-length path for polynomials with unit circle zeros

## Problem

Formalizes polynomial modulus properties, root of unity zeros, and lemniscate bounds.

## References

[EHP55] Erdos, Herzog, Piranian (1955).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1020`

## Build

```bash
lake build Erdos1020
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
