# JSP-000252: Subsets with Reciprocal Sum Equal to One

## Problem

How many subsets S of {1, 2, ..., n} satisfy Σ_{i∈S} 1/i = 1?

## Solution

**Solved** by multiple groups (2024).

## Formalization

This submission verifies the exact count for small n:

- n = 1: exactly 1 subset ({1}) has reciprocal sum 1
- n = 2: exactly 1 subset ({1}) has reciprocal sum 1
- n = 3: exactly 1 subset ({1}) has reciprocal sum 1
- n = 6: exactly 2 subsets have reciprocal sum 1

For n = 6, the 2 subsets are {1} and {2, 3, 6} (since 1/2 + 1/3 + 1/6 = 1).

The proof works by scaling reciprocals to integers via LCM and using
`decide` to enumerate and count.

## Build

```bash
lake build Erdos252
```

Requires Lean 4 v4.34.0 and Mathlib.

## References

- [St24] arXiv:2403.17041 (2024).
- [LiSa24] arXiv:2404.07113 (2024).
- [CFHMPSV24] arXiv:2404.16016 (2024).
