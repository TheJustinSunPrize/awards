# JSP-000307: Lean formalization of descending largest prime factors

## Problem

**JSP-000307**: Can three consecutive integers have strictly decreasing largest
prime factors?

- **Erdős Problem**: Reference [ErPo78], [Ba01]
- **Problem source**: [JSP-000307](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000307)
- **Status**: Solved

## Solution

Balasubramanian (2001) proved that infinitely many such triples exist. The
simplest example is n = 13:

- `maxPrimeFac 13 = 13` (13 is prime)
- `maxPrimeFac 14 = 7` (14 = 2 × 7)
- `maxPrimeFac 15 = 5` (15 = 3 × 5)

with 13 > 7 > 5.

## Formalization

This submission provides a Lean 4 / Mathlib formalization of the existential
witness n = 13, proving:

```lean
theorem jsp_000307 : ∃ n : ℕ, 1 < n ∧
    maxPrimeFac n > maxPrimeFac (n + 1) ∧
    maxPrimeFac (n + 1) > maxPrimeFac (n + 2)
```

This resolves the existential question (the answer is yes). The proof that
infinitely many such triples exist [Ba01] is outside the scope of this
formalization.

## Verification

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib revision**: `v4.34.0`
- **Axioms used**: standard Mathlib axioms only (`propext`, `Classical.choice`,
  `Quot.sound`)
- **Sorry count**: 0
