# JSP-000307: Strictly Decreasing Largest Prime Factors

## Problem

Can three consecutive integers have strictly decreasing largest prime factors?

**Answer:** Yes. Balasubramanian (2001) proved that infinitely many such triples exist.

## Formalization

This submission formalizes a **complete conditional theorem** that provides an explicit
infinite family of such triples:

> For every prime `p` with `p % 6 = 1` such that `(p+1)/2` and `(p+2)/3` are also prime,
> the largest prime factors of `p`, `p+1`, `p+2` are strictly decreasing:
> `maxPrimeFac p > maxPrimeFac (p+1) > maxPrimeFac (p+2)`.

### Proof Strategy

Under the given hypotheses:

1. **`maxPrimeFac p = p`** — since `p` is prime.
2. **`maxPrimeFac (p+1) = (p+1)/2`** — since `p+1 = 2 * ((p+1)/2)`, where `(p+1)/2` is prime and `> 2`.
3. **`maxPrimeFac (p+2) = (p+2)/3`** — since `p+2 = 3 * ((p+2)/3)`, where `(p+2)/3` is prime and `> 3`.
4. **`p > (p+1)/2 > (p+2)/3`** — elementary inequality for `p ≥ 13`.

The key factorizations follow from:
- `p % 6 = 1` implies `p` is odd, so `(p+1) % 2 = 0`.
- `p % 6 = 1` implies `p ≡ 1 (mod 3)`, so `(p+2) % 3 = 0`.

### Examples

The first few primes satisfying all conditions:

| p | (p+1)/2 | (p+2)/3 |
|---|---------|---------|
| 13 | 7 | 5 |
| 37 | 19 | 13 |
| 157 | 79 | 53 |
| 541 | 271 | 181 |
| 877 | 439 | 293 |
| 1201 | 601 | 401 |

Each gives `maxPrimeFac p > maxPrimeFac (p+1) > maxPrimeFac (p+2)`.

### Relationship to the Full Result

The infinitude of such primes `p` is related to Dickson's conjecture (a generalization
of the twin prime conjecture). The conditional theorem here is unconditional — it holds
whenever the primality conditions are met, regardless of whether infinitely many such `p`
exist. Balasubramanian's proof of infinitude uses sieve methods that go beyond what is
currently formalizable in Lean/Mathlib.

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
