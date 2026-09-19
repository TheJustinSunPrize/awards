# JSP-000513: Does list multicolorability persist when both the available-list size and the required number of colors per vertex are doubled?

## Problem

This submission formalizes the doubling relationship for list coloring parameters, verifies counting properties for small graphs, and checks ratio preservation under doubling.

## References

[EFL95] Erdős, Rubin & Taylor, "Choosability in graphs".

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos513`

## Build

```bash
lake build Erdos513
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
