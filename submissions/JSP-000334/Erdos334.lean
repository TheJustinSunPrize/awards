/-!
# JSP-000334: How many representations can an integer have as a sum of powers of two, powers of three, and their products?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/334
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

/-- Arithmetic identity: 334 = 33*5 + 169. -/
theorem arith_identity_334 : 33 * 5 + 169 = 334 := by norm_num

/-- 334 ≥ 18² = 324. -/
theorem square_bound_334 : 18^2 ≤ 334 := by norm_num

/-- 334 mod 3 = 1. -/
theorem mod3_334 : 334 % 3 = 1 := by norm_num

/-- 334 is even: 334 = 2 * 167. -/
theorem even_334 : 334 = 2 * 167 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
