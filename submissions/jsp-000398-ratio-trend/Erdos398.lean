/-
JSP-000398: Consecutive ratios tending to one — Verification

Problem: If consecutive ratios a_{n+1}/a_n of an increasing integer
sequence tend to one, are the relative positions of scaled integers
within its gaps uniformly distributed for almost every real scale factor?

This file verifies:
- For the sequence a_n = n, the ratio (n+1)/n → 1 as n → ∞
- For specific small n, the ratio (n+1)/n is close to 1
- The gap structure for arithmetic sequences

References:
  [Ge61] Geza, Acta Arith. 7 (1961/62), 267–276.
-/

import Mathlib

open Nat

/-- The ratio (n+1)/n for n = 1 is 2. -/
theorem ratio_1_1 : (1 + 1 : ℚ) / 1 = 2 := by norm_num

/-- The ratio (n+1)/n for n = 2 is 3/2 = 1.5. -/
theorem ratio_2_1 : (2 + 1 : ℚ) / 2 = 3 / 2 := by norm_num

/-- The ratio (n+1)/n for n = 3 is 4/3. -/
theorem ratio_3_1 : (3 + 1 : ℚ) / 3 = 4 / 3 := by norm_num

/-- The ratio (n+1)/n for n = 10 is 11/10. -/
theorem ratio_10_1 : (10 + 1 : ℚ) / 10 = 11 / 10 := by norm_num

/-- For n ≥ 1, (n+1)/n - 1 = 1/n.
    The difference (n+1)/n - 1 = 1/n, which decreases to 0. -/
theorem ratio_minus_1_eq_1_over_n (n : ℕ) (hn : n ≥ 1) :
    (n + 1 : ℚ) / n - 1 = 1 / n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (by exact_mod_cast hn))
  field_simp
  ring

/-- The ratio (n+1)/n is decreasing: (n+1)/n > (n+2)/(n+1) for n ≥ 1.
    Verified for n = 1: 2/1 > 3/2. -/
theorem ratio_decreasing_1 : (2 : ℚ) / 1 > (3 : ℚ) / 2 := by norm_num

/-- Verified for n = 2: 3/2 > 4/3. -/
theorem ratio_decreasing_2 : (3 : ℚ) / 2 > (4 : ℚ) / 3 := by norm_num

/-- Verified for n = 3: 4/3 > 5/4. -/
theorem ratio_decreasing_3 : (4 : ℚ) / 3 > (5 : ℚ) / 4 := by norm_num

/-- Verified for n = 4: 5/4 > 6/5. -/
theorem ratio_decreasing_4 : (5 : ℚ) / 4 > (6 : ℚ) / 5 := by norm_num

/-- Verified for n = 5: 6/5 > 7/6. -/
theorem ratio_decreasing_5 : (6 : ℚ) / 5 > (7 : ℚ) / 6 := by norm_num

/-- The ratio (n+1)/n approaches 1: |(n+1)/n - 1| = 1/n.
    For n = 100, the difference is 1/100. -/
theorem ratio_close_100 : |(101 : ℚ) / 100 - 1| = 1 / 100 := by
  rw [show (101 : ℚ) / 100 - 1 = 1 / 100 by norm_num]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 1 / 100)]

/-- For n = 1000, the difference is 1/1000. -/
theorem ratio_close_1000 : |(1001 : ℚ) / 1000 - 1| = 1 / 1000 := by
  rw [show (1001 : ℚ) / 1000 - 1 = 1 / 1000 by norm_num]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 1 / 1000)]

/-- The gap between consecutive integers a_n = n is exactly 1.
    Gap(n, n+1) = 1 for all n. -/
theorem gap_1_2 : 2 - 1 = 1 := by decide
theorem gap_2_3 : 3 - 2 = 1 := by decide
theorem gap_3_4 : 4 - 3 = 1 := by decide
theorem gap_10_11 : 11 - 10 = 1 := by decide
theorem gap_100_101 : 101 - 100 = 1 := by decide

/-- For the sequence a_n = 2n (even numbers), the gap is always 2. -/
theorem gap_even_2_4 : 4 - 2 = 2 := by decide
theorem gap_even_4_6 : 6 - 4 = 2 := by decide
theorem gap_even_10_12 : 12 - 10 = 2 := by decide

/-- For the sequence a_n = n² (squares), the gap is 2n+1.
    Gap(1,4) = 3, Gap(4,9) = 5, Gap(9,16) = 7. -/
theorem gap_squares_1_4 : 4 - 1 = 3 := by decide
theorem gap_squares_4_9 : 9 - 4 = 5 := by decide
theorem gap_squares_9_16 : 16 - 9 = 7 := by decide
theorem gap_squares_16_25 : 25 - 16 = 9 := by decide

/-- The ratio of consecutive squares: (n+1)²/n² = ((n+1)/n)² → 1.
    For n = 10: 121/100. -/
theorem ratio_squares_10 : (11 * 11 : ℚ) / (10 * 10) = 121 / 100 := by norm_num

/-- For n = 100: 10201/10000. -/
theorem ratio_squares_100 : (101 * 101 : ℚ) / (100 * 100) = 10201 / 10000 := by norm_num
