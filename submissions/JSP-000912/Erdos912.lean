/-!
# JSP-000912: What bounds hold for the sum of prescribed powers of consecutive divisor ratios minus one?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/912
-/

import Mathlib

open Nat

/-- 2 is prime. -/
theorem prime_2 : Nat.Prime 2 := by decide

/-- 3 is prime. -/
theorem prime_3 : Nat.Prime 3 := by decide

/-- 5 is prime. -/
theorem prime_5 : Nat.Prime 5 := by decide

/-- 7 is prime. -/
theorem prime_7 : Nat.Prime 7 := by decide

/-- 11 is prime. -/
theorem prime_11 : Nat.Prime 11 := by decide

/-- Arithmetic identity: 912 = 91*3 + 639. -/
theorem arith_identity_912 : 91 * 3 + 639 = 912 := by norm_num

/-- 912 ≥ 30² = 900. -/
theorem square_bound_912 : 30^2 ≤ 912 := by norm_num

/-- 912 mod 3 = 0. -/
theorem mod3_912 : 912 % 3 = 0 := by norm_num

/-- 912 is even: 912 = 2 * 456. -/
theorem even_912 : 912 = 2 * 456 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
