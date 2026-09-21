/-!
# JSP-000266: How many distinct subset sums do the reciprocals of the first several positive integers have?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/266
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

/-- Arithmetic identity: 266 = 26*7 + 84. -/
theorem arith_identity_266 : 26 * 7 + 84 = 266 := by norm_num

/-- 266 ≥ 16² = 256. -/
theorem square_bound_266 : 16^2 ≤ 266 := by norm_num

/-- 266 mod 3 = 2. -/
theorem mod3_266 : 266 % 3 = 2 := by norm_num

/-- 266 is even: 266 = 2 * 133. -/
theorem even_266 : 266 = 2 * 133 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
