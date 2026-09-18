# JSP-000259: Unit Fraction Integer Representations

## Problem

Which integers can be represented by sums of distinct unit fractions with denominators in a finite range?

## Solution

**Solved** by Croot (1999).

## Formalization

This submission verifies:

- 1 = 1/2 + 1/3 + 1/6 is representable (using denominators from {2,3,6})
- 1 cannot be represented using only {1/2} or {1/2, 1/3}
- All 8 subset sums of {1/2, 1/3, 1/6} (scaled by LCM=6 to {3,2,1}) are {0,1,2,3,4,5,6}

Proof method: scale reciprocals to integers via LCM, then use `decide`.

## Build

```bash
lake build Erdos259
```

Requires Lean 4 v4.34.0 and Mathlib.

## References

- [Cr99] Croot, Mathematika 46 (1999), 359-372.
