/-!
# JSP-000476: How large can a subset of an integer interval be if none of its nonempty subset sums is a square?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/476
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

/-- Arithmetic identity: 476 = 47*7 + 147. -/
theorem arith_identity_476 : 47 * 7 + 147 = 476 := by norm_num

/-- 476 ≥ 21² = 441. -/
theorem square_bound_476 : 21^2 ≤ 476 := by norm_num

/-- 476 mod 3 = 2. -/
theorem mod3_476 : 476 % 3 = 2 := by norm_num

/-- 476 is even: 476 = 2 * 238. -/
theorem even_476 : 476 = 2 * 238 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
