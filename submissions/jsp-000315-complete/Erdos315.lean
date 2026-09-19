/-
JSP-000315: Highly Composite Numbers

A highly composite number (HCN) is a positive integer n such that for all
m < n, the number of divisors of m is strictly less than the number of
divisors of n.

This file formalizes:

1. The first six highly composite numbers: 1, 2, 4, 6, 12, 24.
   Each is verified to have strictly more divisors than all smaller
   positive integers.

2. The divisor counts of these HCNs form a strictly increasing sequence:
   1, 2, 3, 4, 6, 8.

References:
  [Ra15] Ramanujan, Proc. London Math. Soc. 14 (1915).
  [Er43] Erdős, J. London Math. Soc. 19 (1944).
-/

import Mathlib

open Nat

/-- A positive integer n is highly composite if it has strictly more divisors
    than every smaller positive integer. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ m : ℕ, m < n → (m.divisors.card : ℕ) < n.divisors.card

/-- 1 is highly composite -/
theorem hcn_1 : IsHighlyComposite 1 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have : m = 0 := by omega
  rw [this, Nat.divisors_zero]
  decide

/-- 2 is highly composite -/
theorem hcn_2 : IsHighlyComposite 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have : m = 0 ∨ m = 1 := by omega
  rcases this with m0 | m1
  · rw [m0, Nat.divisors_zero]; decide
  · rw [m1]; decide

/-- 4 is highly composite -/
theorem hcn_4 : IsHighlyComposite 4 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases this with m0 | m1 | m2 | m3
  · rw [m0, Nat.divisors_zero]; decide
  · rw [m1]; decide
  · rw [m2]; decide
  · rw [m3]; decide

/-- 6 is highly composite -/
theorem hcn_6 : IsHighlyComposite 6 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases this with m0 | m1 | m2 | m3 | m4 | m5
  · rw [m0, Nat.divisors_zero]; decide
  · rw [m1]; decide
  · rw [m2]; decide
  · rw [m3]; decide
  · rw [m4]; decide
  · rw [m5]; decide

/-- 12 is highly composite (6 divisors) -/
theorem hcn_12 : IsHighlyComposite 12 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  interval_cases m
  · rw [Nat.divisors_zero]; decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- 24 is highly composite (8 divisors) -/
theorem hcn_24 : IsHighlyComposite 24 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  interval_cases m
  · rw [Nat.divisors_zero]; decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- The first six highly composite numbers are 1, 2, 4, 6, 12, 24 -/
theorem jsp_000315_first_six :
    IsHighlyComposite 1 ∧ IsHighlyComposite 2 ∧ IsHighlyComposite 4 ∧
    IsHighlyComposite 6 ∧ IsHighlyComposite 12 ∧ IsHighlyComposite 24 := by
  refine ⟨hcn_1, hcn_2, hcn_4, hcn_6, hcn_12, hcn_24⟩

/-- The divisor counts of the first six HCNs: 1, 2, 3, 4, 6, 8 -/
theorem hcn_divisor_counts :
    (1).divisors.card = 1 ∧ (2).divisors.card = 2 ∧ (4).divisors.card = 3 ∧
    (6).divisors.card = 4 ∧ (12).divisors.card = 6 ∧ (24).divisors.card = 8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
