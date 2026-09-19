# JSP-000385: Can all natural numbers be permuted so that every adjacent pair has prime sum?

## Problem

This submission formalizes scoped components of the problem: specific small permutations of natural numbers where adjacent pairs have prime sums, and verifications that key sums are prime.

## References

[ErGr80] Erdős & Graham, "Old and new problems and results in combinatorial number theory" — Monographies de L'Enseignement Mathematique (1980).

## Formalization

This file provides Lean 4 formalization of scoped components of the problem.
All theorems are proved using `decide` (native decision procedures) with no
axioms or `sorry`.

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib version**: `v4.34.0`
- **Library name**: `Erdos385`

## Build

```bash
lake build Erdos385
```

## Verification

- See `verification/sha256.txt` for the SHA256 hash of the Lean source file.
- See `verification/toolchain.txt` for the toolchain version.
- See `verification/axioms.txt` for the axioms used (none).
