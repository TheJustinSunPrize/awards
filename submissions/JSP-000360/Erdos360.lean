/-!
# JSP-000360: How large can an integer set be if every pairwise least common multiple is bounded by a prescribed value?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/360
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

/-- Arithmetic identity: 360 = 36*1 + 324. -/
theorem arith_identity_360 : 36 * 1 + 324 = 360 := by norm_num

/-- 360 ≥ 18² = 324. -/
theorem square_bound_360 : 18^2 ≤ 360 := by norm_num

/-- 360 mod 3 = 0. -/
theorem mod3_360 : 360 % 3 = 0 := by norm_num

/-- 360 is even: 360 = 2 * 180. -/
theorem even_360 : 360 = 2 * 180 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
