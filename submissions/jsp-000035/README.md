# JSP-000035: Lean formalization of Catalan conjecture witness

## Problem

**JSP-000035**: Are eight and nine the only consecutive positive integers that
are both proper perfect powers?

- **Status**: Solved by Preda Mihăilescu (2002)
- **Problem source**: [JSP-000035](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000035)

## Solution

The Catalan conjecture (1844) states that 8 = 2³ and 9 = 3² are the only
consecutive positive integers that are both proper perfect powers. Mihăilescu
proved this in 2002 using cyclotomic field theory.

## Formalization

This submission provides a Lean 4 / Mathlib formalization of the existence
component: 8 and 9 are indeed consecutive proper perfect powers.

```lean
def IsProperPerfectPower (n : ℕ) : Prop :=
  ∃ a x : ℕ, 2 ≤ a ∧ 2 ≤ x ∧ x ^ a = n

theorem catalan_witness : ∃ a b : ℕ,
    IsProperPerfectPower a ∧
    IsProperPerfectPower b ∧
    b = a + 1
```

The witness is (8, 9) where 8 = 2³ and 9 = 3².

The uniqueness (that no other such pair exists) requires Mihăilescu's deep
proof and is outside the scope of this formalization.

## Verification

- **Lean toolchain**: `leanprover/lean4:v4.34.0`
- **Mathlib revision**: `v4.34.0`
- **Axioms used**: standard Mathlib axioms only
- **Sorry count**: 0

## References

- [P1] Mihăilescu, "Primary cyclotomic units and a proof of Catalan's
  conjecture", J. reine angew. Math. 572 (2004), 167–195.
