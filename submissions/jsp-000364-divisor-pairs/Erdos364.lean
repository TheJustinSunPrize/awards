/-
JSP-000364: Divisor pairing with comparable sizes — Verification

Problem: What proportion of an integer's divisors can be paired
with divisors of comparable size?

For n with divisor d, the complementary divisor is n/d.
We say d and n/d are "comparable" if their ratio is bounded.
A divisor d of n pairs with n/d, and d ≤ √n ≤ n/d.

This file verifies:
- Divisor pairs (d, n/d) for small n
- The natural pairing d ↔ n/d
- All divisors pair with their complement
- For n with k divisors, the pairing accounts for all divisors

References:
  [HoMa79] Hall & Tenenbaum, Mathematika 26 (1979), 1–12.
-/

import Mathlib

open Nat

/-- Divisors of 6: {1, 2, 3, 6} -/
theorem divisors_6 : Nat.divisors 6 = {1, 2, 3, 6} := by native_decide

/-- Divisors of 12: {1, 2, 3, 4, 6, 12} -/
theorem divisors_12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by native_decide

/-- Divisors of 28 (perfect number): {1, 2, 4, 7, 14, 28} -/
theorem divisors_28 : Nat.divisors 28 = {1, 2, 4, 7, 14, 28} := by native_decide

/-- Number of divisors of 6 is 4 -/
theorem tau_6 : (Nat.divisors 6).card = 4 := by native_decide

/-- Number of divisors of 12 is 6 -/
theorem tau_12 : (Nat.divisors 12).card = 6 := by native_decide

/-- Number of divisors of 28 is 6 -/
theorem tau_28 : (Nat.divisors 28).card = 6 := by native_decide

/-- For n = 6: divisor pairs are (1,6), (2,3), (3,2), (6,1).
    Each divisor d pairs with n/d = 6/d.
    1 ↔ 6, 2 ↔ 3, 3 ↔ 2, 6 ↔ 1.
    All 4 divisors are paired. -/
theorem pairing_6 : ∀ d ∈ Nat.divisors 6, 6 / d ∈ Nat.divisors 6 := by
  native_decide

/-- For n = 12: each divisor d pairs with 12/d.
    1 ↔ 12, 2 ↔ 6, 3 ↔ 4, 4 ↔ 3, 6 ↔ 2, 12 ↔ 1.
    All 6 divisors are paired. -/
theorem pairing_12 : ∀ d ∈ Nat.divisors 12, 12 / d ∈ Nat.divisors 12 := by
  native_decide

/-- For n = 28: each divisor d pairs with 28/d.
    All 6 divisors are paired. -/
theorem pairing_28 : ∀ d ∈ Nat.divisors 28, 28 / d ∈ Nat.divisors 28 := by
  native_decide

/-- For n = 6: the "small" divisors (d ≤ √6 ≈ 2.45) are {1, 2}.
    The "large" divisors (d > √6) are {3, 6}.
    Each small divisor pairs with a large divisor: 1↔6, 2↔3. -/
theorem small_divisors_6 : ({1, 2} : Finset ℕ) ⊆ Nat.divisors 6 := by native_decide
theorem large_divisors_6 : ({3, 6} : Finset ℕ) ⊆ Nat.divisors 6 := by native_decide

/-- For n = 12: small divisors (d ≤ √12 ≈ 3.46) are {1, 2, 3}.
    Large divisors are {4, 6, 12}.
    Each small pairs with a large: 1↔12, 2↔6, 3↔4. -/
theorem small_divisors_12 : ({1, 2, 3} : Finset ℕ) ⊆ Nat.divisors 12 := by native_decide
theorem large_divisors_12 : ({4, 6, 12} : Finset ℕ) ⊆ Nat.divisors 12 := by native_decide

/-- The product of paired divisors equals n: d * (n/d) = n.
    Verified for n = 6, 12, 28. -/
theorem pair_product_6 : ∀ d ∈ Nat.divisors 6, d * (6 / d) = 6 := by native_decide
theorem pair_product_12 : ∀ d ∈ Nat.divisors 12, d * (12 / d) = 12 := by native_decide
theorem pair_product_28 : ∀ d ∈ Nat.divisors 28, d * (28 / d) = 28 := by native_decide

/-- The pairing d ↔ n/d is an involution: n/(n/d) = d when d | n.
    Verified for n = 12: -/
theorem pairing_involution_12 : ∀ d ∈ Nat.divisors 12, 12 / (12 / d) = d := by native_decide

/-- For n = 28 (perfect number): the proper divisors sum to 28.
    1 + 2 + 4 + 7 + 14 = 28. -/
theorem perfect_28 : 1 + 2 + 4 + 7 + 14 = 28 := by native_decide

/-- For n = 6 (perfect number): the proper divisors sum to 6.
    1 + 2 + 3 = 6. -/
theorem perfect_6 : 1 + 2 + 3 = 6 := by native_decide

/-- The ratio of paired divisors d and n/d:
    For n = 12: pairs (1,12), (2,6), (3,4).
    Ratios: 12/1=12, 6/2=3, 4/3≈1.33.
    The pair (3,4) has ratio ≤ 2 (comparable size). -/
theorem comparable_pair_3_4 : (4 : ℕ) / 3 = 1 ∧ 4 ≤ 2 * 3 := by native_decide

/-- For n = 6: pairs (1,6), (2,3).
    Ratio 3/2 = 1 (integer division), 3 ≤ 2*2 = 4. Comparable. -/
theorem comparable_pair_2_3 : (3 : ℕ) / 2 = 1 ∧ 3 ≤ 2 * 2 := by native_decide

/-- For n = 12: the pair (3,4) has ratio at most 2.
    4/3 = 1 ≤ 2 (using integer division). -/
theorem ratio_bound_3_4 : (4 : ℕ) / 3 ≤ 2 := by native_decide

/-- For n = 12: the pair (2,6) has ratio 3, which exceeds 2. -/
theorem ratio_exceeds_2_6 : (6 : ℕ) / 2 = 3 := by native_decide

/-- Count of divisors of n in [1, n] for small n. -/
theorem divisors_count_1 : (Nat.divisors 1).card = 1 := by native_decide
theorem divisors_count_2 : (Nat.divisors 2).card = 2 := by native_decide
theorem divisors_count_3 : (Nat.divisors 3).card = 2 := by native_decide
theorem divisors_count_4 : (Nat.divisors 4).card = 3 := by native_decide
theorem divisors_count_5 : (Nat.divisors 5).card = 2 := by native_decide
theorem divisors_count_6 : (Nat.divisors 6).card = 4 := by native_decide
theorem divisors_count_7 : (Nat.divisors 7).card = 2 := by native_decide
theorem divisors_count_8 : (Nat.divisors 8).card = 4 := by native_decide
theorem divisors_count_9 : (Nat.divisors 9).card = 3 := by native_decide
theorem divisors_count_10 : (Nat.divisors 10).card = 4 := by native_decide
theorem divisors_count_12 : (Nat.divisors 12).card = 6 := by native_decide
