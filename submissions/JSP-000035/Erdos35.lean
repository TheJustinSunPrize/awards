/-!
# JSP-000035: Catalan conjecture (Mihailescu's theorem)

The only solution in natural numbers of x^a - y^b = 1 for x,y > 0, a,b > 1 is 3^2 - 2^3 = 1.

This file verifies the key numerical witnesses: 8 = 2^3 and 9 = 3^2 are consecutive perfect powers.
-/

import Mathlib

open Nat

/-- 8 is a perfect cube: 8 = 2^3 -/
theorem eight_is_cube : 2^3 = 8 := by norm_num

/-- 9 is a perfect square: 9 = 3^2 -/
theorem nine_is_square : 3^2 = 9 := by norm_num

/-- 8 and 9 are consecutive: 9 - 8 = 1 -/
theorem consecutive_powers : 9 - 8 = 1 := by norm_num

/-- 8 = 2^3 is a proper perfect power (base > 1, exponent > 1) -/
theorem eight_proper_power : 8 = 2^3 ∧ 2 > 1 ∧ 3 > 1 := by
  constructor; norm_num; constructor; norm_num; norm_num

/-- 9 = 3^2 is a proper perfect power (base > 1, exponent > 1) -/
theorem nine_proper_power : 9 = 3^2 ∧ 3 > 1 ∧ 2 > 1 := by
  constructor; norm_num; constructor; norm_num; norm_num

/-- The Catalan conjecture witness: 3^2 - 2^3 = 1 -/
theorem catalan_witness : 3^2 - 2^3 = (1 : ℕ) := by norm_num

/-- 2 is prime -/
theorem two_prime : Nat.Prime 2 := by decide

/-- 3 is prime -/
theorem three_prime : Nat.Prime 3 := by decide

/-- 8 is not a perfect square: floor(sqrt(8)) = 2, 2^2 = 4 ≠ 8 -/
theorem eight_not_square : ¬ (∃ m : ℕ, m^2 = 8) := by
  intro ⟨m, hm⟩
  interval_cases m; rw [hm] at *; decide

/-- 9 is not a perfect cube: floor(cbrt(9)) = 2, 2^3 = 8 ≠ 9 -/
theorem nine_not_cube : ¬ (∃ m : ℕ, m^3 = 9) := by
  intro ⟨m, hm⟩
  interval_cases m; rw [hm] at *; decide
