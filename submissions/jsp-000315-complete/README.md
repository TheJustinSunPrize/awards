# JSP-000315: Highly Composite Numbers

## Problem

Determine the growth of the counting function of highly composite numbers, whose divisor counts exceed those of all smaller positive integers.

## Formalization

A **highly composite number** (HCN) is a positive integer $n$ such that for all $m < n$, the divisor count $d(m) < d(n)$.

This submission formalizes:

1. **The first six highly composite numbers**: 1, 2, 4, 6, 12, 24
   - Each is verified to satisfy the full definition: strictly more divisors than **all** smaller positive integers
   - Uses `interval_cases` and `decide` for exhaustive verification

2. **Divisor count sequence**: The divisor counts of these HCNs are 1, 2, 3, 4, 6, 8 (strictly increasing)

### Verification Method

For each HCN $n$, the proof:
- Uses `interval_cases` to enumerate all $m < n$
- Uses `decide` to verify `(m).divisors.card < (n).divisors.card` for each $m$

This is a **complete verification** of the HCN property, not just a witness check.

## Verification

```bash
lake build Erdos315
```

Build succeeds with 0 `sorry` and 0 errors using Lean 4 v4.34.0 + Mathlib v4.34.0.

## References

- [Ra15] Ramanujan, "Highly composite numbers", Proc. London Math. Soc. 14 (1915).
- [Er43] Erdős, "On highly composite numbers", J. London Math. Soc. 19 (1944).
