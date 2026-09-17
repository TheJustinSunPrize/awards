# JSP-000307: Strictly Monotone Largest Prime Factors in Consecutive Integers

## Problem

Can three consecutive integers have strictly decreasing (or increasing) largest prime factors?

**Answer:** Yes. Balasubramanian (2001) proved that infinitely many such triples exist in both directions.

## Formalization

This submission formalizes **two complete conditional theorems** providing explicit infinite families:

### 1. Decreasing Theorem

For every prime `p` with `p % 6 = 1` such that `(p+1)/2` and `(p+2)/3` are also prime:
```
maxPrimeFac p > maxPrimeFac (p+1) > maxPrimeFac (p+2)
```

### 2. Increasing Theorem

For every prime `q > 3` such that `(3q+1)/2` and `3q+2` are also prime:
```
maxPrimeFac (3q) < maxPrimeFac (3q+1) < maxPrimeFac (3q+2)
```

### Proof Strategy

Both proofs use:
1. Exact factorization of consecutive integers (e.g., `p+1 = 2 * ((p+1)/2)`)
2. `maxPrimeFac` of a product `a * b` where `a, b` are prime equals `max(a, b)`
3. Elementary inequalities between the prime factors

### Examples

**Decreasing** (p, (p+1)/2, (p+2)/3):

| p | (p+1)/2 | (p+2)/3 |
|---|---------|---------|
| 13 | 7 | 5 |
| 37 | 19 | 13 |
| 157 | 79 | 53 |
| 541 | 271 | 181 |
| 877 | 439 | 293 |

**Increasing** (q, (3q+1)/2, 3q+2):

| q | (3q+1)/2 | 3q+2 |
|---|---------|-------|
| 7 | 11 | 23 |
| 19 | 29 | 59 |
| 59 | 89 | 179 |
| 127 | 191 | 383 |
| 167 | 251 | 503 |

## Verification

```bash
lake build Erdos307
```

Build succeeds with 0 `sorry` and 0 errors using Lean 4 v4.34.0 with Mathlib v4.34.0.

## References

- [ErPo78] Erdős and Pomerance, "On the largest prime factors of n and n+1",
  Aequationes Math. 16 (1978), 311–321.
- [Ba01] Balasubramanian, "On triplets with descending largest prime factors",
  Studia Sci. Math. Hungar. 36 (2001), 45–50.
