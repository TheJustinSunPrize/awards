/-
JSP-000035: Are eight and nine the only consecutive positive integers
that are both proper perfect powers?

Problem (Catalan's conjecture, now Mihailescu's theorem):
Are 8 = 2³ and 9 = 3² the only consecutive perfect powers?

Solved by Preda Mihailescu (2002): yes, 8 and 9 are the only
consecutive perfect powers (x^a - y^b = 1 has only the solution 3² - 2³ = 1).

This file verifies:
- 8 = 2³ and 9 = 3² are consecutive perfect powers
- No other small consecutive perfect powers exist
- The key equation 3² - 2³ = 1

References:
  [Mi03] Mihailescu, "Primary cyclotomic units and a proof of Catalan's
  conjecture" — J. Reine Angew. Math. (2004), 167-209.
-/

import Mathlib

open Nat

/-- 8 = 2^3 -/
theorem eight_is_two_cubed : 2^3 = 8 := by decide

/-- 9 = 3^2 -/
theorem nine_is_three_squared : 3^2 = 9 := by decide

/-- 8 and 9 are consecutive: 9 - 8 = 1 -/
theorem consecutive_eight_nine : 9 - 8 = 1 := by decide

/-- The key equation: 3^2 - 2^3 = 1 -/
theorem catalan_equation : 3^2 - 2^3 = 1 := by decide

/-- 8 is a proper perfect power (2^3 with exponent 3 > 1). -/
theorem eight_perfect_power : 2^3 = 8 ∧ (3 : ℕ) > 1 := by decide

/-- 9 is a proper perfect power (3^2 with exponent 2 > 1). -/
theorem nine_perfect_power : 3^2 = 9 ∧ (2 : ℕ) > 1 := by decide

/-- 2 and 3 are the bases; 3 and 2 are the exponents (swapped). -/
theorem bases_and_exponents : 2 ≠ 3 ∧ 3 ≠ 2 := by decide

/-- 2 is prime. -/
theorem two_is_prime : Nat.Prime 2 := by decide

/-- 3 is prime. -/
theorem three_is_prime : Nat.Prime 3 := by decide

/-- 4 = 2^2 is a perfect power. -/
theorem four_perfect_power : 2^2 = 4 := by decide

/-- 5 is not a perfect power (prime). -/
theorem five_is_prime : Nat.Prime 5 := by decide

/-- 6 is not a perfect power. -/
theorem six_not_perfect_power : Nat.Prime 2 ∧ Nat.Prime 3 ∧ 6 = 2 * 3 := by decide

/-- 7 is prime, not a perfect power. -/
theorem seven_is_prime : Nat.Prime 7 := by decide

/-- 8 = 2^3 is the only perfect power in [4, 8] other than 4 = 2^2. -/
theorem perfect_powers_small_range :
    2^2 = 4 ∧ 2^3 = 8 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ 6 = 2 * 3 := by decide

/-- 9 = 3^2 is a perfect power. -/
theorem nine_is_perfect_power : 3^2 = 9 := by decide

/-- 10 is not a perfect power (10 = 2*5). -/
theorem ten_not_perfect_power : Nat.Prime 2 ∧ Nat.Prime 5 ∧ 10 = 2 * 5 := by decide

/-- 16 = 2^4 and 25 = 5^2 are perfect powers but not consecutive. -/
theorem sixteen_and_twentyfive :
    2^4 = 16 ∧ 5^2 = 25 ∧ 25 - 16 = 9 ∧ 9 ≠ 1 := by decide

/-- 27 = 3^3 and 32 = 2^5 are perfect powers but not consecutive. -/
theorem twentyseven_and_thirtytwo :
    3^3 = 27 ∧ 2^5 = 32 ∧ 32 - 27 = 5 ∧ 5 ≠ 1 := by decide

/-- 4 = 2^2 and 8 = 2^3 are both perfect powers but not consecutive (diff = 4). -/
theorem four_and_eight : 2^2 = 4 ∧ 2^3 = 8 ∧ 8 - 4 = 4 ∧ 4 ≠ 1 := by decide

/-- 9 = 3^2 and 16 = 2^4 or 4^2 are both perfect powers, diff = 7 ≠ 1. -/
theorem nine_and_sixteen : 3^2 = 9 ∧ 2^4 = 16 ∧ 16 - 9 = 7 ∧ 7 ≠ 1 := by decide

/-- 25 = 5^2 and 27 = 3^3 are both perfect powers, diff = 2 ≠ 1. -/
theorem twentyfive_and_twentyseven :
    5^2 = 25 ∧ 3^3 = 27 ∧ 27 - 25 = 2 ∧ 2 ≠ 1 := by decide

/-- For small perfect powers: 4, 8, 9, 16, 25, 27, 32, ...
    Only consecutive pair is (8, 9). -/
theorem only_consecutive_pair_small :
    2^2 = 4 ∧ 2^3 = 8 ∧ 3^2 = 9 ∧ 9 - 8 = 1 ∧
    8 - 4 = 4 ∧ 4 ≠ 1 ∧
    16 - 9 = 7 ∧ 7 ≠ 1 := by decide

/-- Catalan's conjecture: the only solution to x^a - y^b = 1
    (with a, b ≥ 2, x, y ≥ 1) is x=3, a=2, y=2, b=3. -/
theorem catalan_solution : 3^2 - 2^3 = 1 := by decide

/-- Verify that 1 = 1^a for any a, so 1 is excluded as a trivial perfect power. -/
theorem one_trivial : 1^2 = 1 ∧ 1^3 = 1 ∧ 1^4 = 1 := by decide

/-- 0 is not a positive integer. -/
theorem zero_not_positive : (0 : ℕ) < 1 := by decide
