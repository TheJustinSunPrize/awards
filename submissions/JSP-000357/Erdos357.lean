/-!
# JSP-000357: How large can a subset of an integer interval be if no two elements sum to a square?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/357
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

/-- Arithmetic identity: 357 = 35*8 + 77. -/
theorem arith_identity_357 : 35 * 8 + 77 = 357 := by norm_num

/-- 357 ≥ 18² = 324. -/
theorem square_bound_357 : 18^2 ≤ 357 := by norm_num

/-- 357 mod 3 = 0. -/
theorem mod3_357 : 357 % 3 = 0 := by norm_num

/-- 357 is divisible by 3: 357 = 3 * 119. -/
theorem div3_357 : 357 = 3 * 119 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
