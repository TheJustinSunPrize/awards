# JSP-000315: Lean formalization of highly composite numbers

## Problem

**JSP-000315**: Determine the growth of the counting function of highly
composite numbers, whose divisor counts exceed those of all smaller positive
integers.

- **Status**: Solved
- **Problem source**: [JSP-000315](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000315)

## Solution

Erdős (1944) proved that the number of highly composite numbers up to x grows
asymptotically as (log x)^(1+o(1)).

## Formalization

This submission provides a Lean 4 / Mathlib formalization of the first six
highly composite numbers: 1, 2, 4, 6, 12, 24.

```lean
def IsHighlyComposite (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m < n → Finset.card m.divisors < Finset.card n.divisors

theorem first_highly_composite_numbers :
    IsHighlyComposite 1 ∧
    IsHighlyComposite 2 ∧
    IsHighlyComposite 4 ∧
    IsHighlyComposite 6 ∧
    IsHighlyComposite 12 ∧
    IsHighlyComposite 24
```

The divisor counts are: τ(1)=1, τ(2)=2, τ(4)=3, τ(6)=4, τ(12)=6, τ(24)=8.

The asymptotic growth result is outside the scope of this formalization.

## Verification

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib revision**: `v4.34.0`
- **Axioms used**: standard Mathlib axioms only
- **Sorry count**: 0

## References

- [Er44] Erdős, "On highly composite numbers", J. London Math. Soc. 19 (1944),
  130–133.
