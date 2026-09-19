# JSP-001000: Growth rate of integer-ratio-free sets

## Problem

Formalizes properties of sets with no integer ratios between elements and growth bounds.

## References

[Er80] Erdos (1980).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos1000`

## Build

```bash
lake build Erdos1000
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
