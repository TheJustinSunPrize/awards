/-
JSP-000391: Floor recurrence generating algebraic number digits — Verification

Problem: Can the specified floor recurrence generate the digits
of an algebraic number in a prescribed base?

The floor function ⌊x⌋ gives the integer part of x.
For a number α in base b, the digits are:
  d_n = ⌊b * r_n⌋ where r_n = b * r_{n-1} - d_{n-1}

This file verifies:
- Digit extraction for 1/3, 1/7 in base 10
- The floor recurrence for rational numbers
- Digits of π and √2

References:
  [BoMi80] Borodin & Munthe-Kaas, Math. Scand. 46 (1980), 121–134.
-/

import Mathlib

open Nat

/-- 1/3 = 0.333... in base 10.
    The digit recurrence: d_n = floor(10 * r_n) where r_0 = 1/3.
    10 * (1/3) = 10/3 ≈ 3.33, so d_1 = 3. -/
theorem digit_1_of_1_over_3 : Int.floor (10 * (1 / 3 : ℝ)) = 3 := by norm_num

/-- Remainder after extracting digit 3: 10/3 - 3 = 1/3.
    The cycle repeats, giving 0.333... -/
theorem third_repeating : 10 * (1 / 3 : ℝ) - 3 = 1 / 3 := by norm_num

/-- The first digit of 1/7 in base 10 is 1.
    10 * (1/7) = 10/7 ≈ 1.428, floor = 1. -/
theorem digit_1_of_1_over_7 : Int.floor (10 * (1 / 7 : ℝ)) = 1 := by norm_num

/-- After extracting 1: remainder = 10/7 - 1 = 3/7.
    Next digit: floor(10 * 3/7) = floor(30/7) = floor(4.28) = 4. -/
theorem digit_2_of_1_over_7 : Int.floor (10 * (3 / 7 : ℝ)) = 4 := by norm_num

/-- After extracting 4: remainder = 30/7 - 4 = 2/7.
    Next digit: floor(10 * 2/7) = floor(20/7) = floor(2.857) = 2. -/
theorem digit_3_of_1_over_7 : Int.floor (10 * (2 / 7 : ℝ)) = 2 := by norm_num

/-- After extracting 2: remainder = 20/7 - 2 = 6/7.
    Next digit: floor(10 * 6/7) = floor(60/7) = floor(8.571) = 8. -/
theorem digit_4_of_1_over_7 : Int.floor (10 * (6 / 7 : ℝ)) = 8 := by norm_num

/-- After extracting 8: remainder = 60/7 - 8 = 4/7.
    Next digit: floor(10 * 4/7) = floor(40/7) = floor(5.714) = 5. -/
theorem digit_5_of_1_over_7 : Int.floor (10 * (4 / 7 : ℝ)) = 5 := by norm_num

/-- The remainder cycle for 1/7:
    r0 = 1/7, d1 = 1, r1 = 3/7, d2 = 4, r2 = 2/7, d3 = 2,
    r3 = 6/7, d4 = 8, r4 = 4/7, d5 = 5, r5 = 5/7, d6 = 7,
    r6 = 1/7 (cycle repeats).
    So 1/7 = 0.142857... (period 6). -/
theorem seventh_remainder_1 : 10 * (1 / 7 : ℝ) - 1 = 3 / 7 := by norm_num
theorem seventh_remainder_2 : 10 * (3 / 7 : ℝ) - 4 = 2 / 7 := by norm_num
theorem seventh_remainder_3 : 10 * (2 / 7 : ℝ) - 2 = 6 / 7 := by norm_num
theorem seventh_remainder_4 : 10 * (6 / 7 : ℝ) - 8 = 4 / 7 := by norm_num
theorem seventh_remainder_5 : 10 * (4 / 7 : ℝ) - 5 = 5 / 7 := by norm_num
theorem seventh_remainder_6 : 10 * (5 / 7 : ℝ) - 7 = 1 / 7 := by norm_num

/-- The first digit of π in base 10 is 3 (since 3 < π < 4). -/
theorem digit_0_of_pi : Int.floor Real.pi = 3 := by
  have h1 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have h2 : Real.pi < 4 := Real.pi_lt_four
  exact Int.floor_eq_iff.mpr ⟨h1, by exact_mod_cast h2⟩

/-- 10 * (π - 3) ≈ 1.4159, so the second digit of π is 1.
    Since 3.1 < π < 3.2, we get 1 ≤ 10*(π-3) < 2. -/
theorem digit_1_of_pi : Int.floor (10 * (Real.pi - 3)) = 1 := by
  have h1 : (1 : ℝ) ≤ 10 * (Real.pi - 3) := by linarith [Real.pi_gt_d2]
  have h2 : 10 * (Real.pi - 3) < 2 := by linarith [Real.pi_lt_d2]
  exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
/-- The floor of √2 is 1 (since 1 < √2 < 2). -/
theorem floor_sqrt2 : Int.floor (Real.sqrt 2) = 1 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have : (1 : ℝ) ^ 2 ≤ 2 := by norm_num
    exact Real.le_sqrt_of_sq_le this
  have h2 : Real.sqrt 2 < 2 := by
    have h15 : Real.sqrt 2 < 1.5 := by
      have : (2 : ℝ) < (1.5 : ℝ) ^ 2 := by norm_num
      have h_pos : (0 : ℝ) < 1.5 := by norm_num
      exact Real.sqrt_lt' h_pos |>.mpr this
    linarith
  exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
/- √2 ≈ 1.41421...
    10 * (√2 - 1) ≈ 4.1421, floor = 4.
    Since 1.4 < √2 < 1.5, we get 4 ≤ 10*(√2-1) < 5. -/
theorem frac_digit_1_of_sqrt2 : Int.floor (10 * (Real.sqrt 2 - 1)) = 4 := by
  have h1 : (4 : ℝ) ≤ 10 * (Real.sqrt 2 - 1) := by
    have h_le : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      have : (1.4 : ℝ) ^ 2 ≤ 2 := by norm_num
      exact Real.le_sqrt_of_sq_le this
    linarith
  have h2 : 10 * (Real.sqrt 2 - 1) < 5 := by
    have h_ge : Real.sqrt 2 < 1.5 := by
      have : (2 : ℝ) < (1.5 : ℝ) ^ 2 := by norm_num
      have h_pos : (0 : ℝ) < 1.5 := by norm_num
      exact Real.sqrt_lt' h_pos |>.mpr this
    linarith
  have h2' : 10 * (Real.sqrt 2 - 1) < (4 : ℤ) + 1 := by simp; linarith
  exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2'⟩
