/-
JSP-000315: Growth of the counting function of highly composite numbers

A highly composite number is a positive integer that has more divisors than
any smaller positive integer. Erdős (1944) studied their asymptotic density.

This file formalizes the scoped component: the first six highly composite
numbers are 1, 2, 4, 6, 12, 24, each having strictly more divisors than all
preceding positive integers.

The asymptotic growth result of Erdős is outside the scope of this
formalization.

Reference:
  [Er44] Erdős, "On highly composite numbers", J. London Math. Soc. 19 (1944),
         130–133.
-/

import Mathlib

open Nat

/-- A highly composite number: n is highly composite if the number of divisors
  of n exceeds the number of divisors of every positive integer m < n. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m < n → Finset.card m.divisors < Finset.card n.divisors

/-- JSP-000315 (scoped component): The first six highly composite numbers
are 1, 2, 4, 6, 12, 24.

  |1.divisors| = 1, |2.divisors| = 2, |4.divisors| = 3,
  |6.divisors| = 4, |12.divisors| = 6, |24.divisors| = 8. -/
theorem first_highly_composite_numbers :
    IsHighlyComposite 1 ∧
    IsHighlyComposite 2 ∧
    IsHighlyComposite 4 ∧
    IsHighlyComposite 6 ∧
    IsHighlyComposite 12 ∧
    IsHighlyComposite 24 := by
  unfold IsHighlyComposite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- n = 1: no m with 1 ≤ m < 1
    intro m hm hlt
    omega
  · -- n = 2: only m = 1
    intro m hm hlt
    interval_cases m
    decide
  · -- n = 4: m ∈ {1, 2, 3}
    intro m hm hlt
    interval_cases m
    all_goals decide
  · -- n = 6: m ∈ {1, ..., 5}
    intro m hm hlt
    interval_cases m
    all_goals decide
  · -- n = 12: m ∈ {1, ..., 11}
    intro m hm hlt
    interval_cases m
    all_goals decide
  · -- n = 24: m ∈ {1, ..., 23}
    intro m hm hlt
    interval_cases m
    all_goals decide
