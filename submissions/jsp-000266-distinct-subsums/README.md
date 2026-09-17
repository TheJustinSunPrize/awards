# JSP-000266: Distinct Subset Sums of Reciprocals

## Problem

How many distinct subset sums do the reciprocals of the first several
positive integers have? That is, how many distinct values does
Σ_{i∈S} 1/i take over all S ⊆ {1, ..., n}?

## Solution

**Solved** by Bleicher and Erdős (1975), with subsequent improvements.

## Formalization

This submission verifies the exact count for small n:

- n = 1: 2 distinct sums (= 2^1)
- n = 2: 4 distinct sums (= 2^2)
- n = 3: 8 distinct sums (= 2^3)

For each n, all 2^n subsets give distinct sums. This is verified by
scaling reciprocals to integers (via LCM) and using `decide` to count
distinct subset sums:

- {1, 1/2} → LCM=2 → {2, 1} → 4 distinct sums
- {1, 1/2, 1/3} → LCM=6 → {6, 3, 2} → 8 distinct sums

## Build

```bash
lake build Erdos266
```

Requires Lean 4 v4.34.0 and Mathlib.

## References

- [BlEr75] Bleicher and Erdős, "The number of distinct subsums of
  Σ_{1}^{N} 1/i", Math. Comp. 29 (1975), 29-42.
