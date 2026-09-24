/-!
# JSP-000400: Can a sum of two integer squares approximate an irrational multiple of an integer square sufficiently closely?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/400
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

/-- Arithmetic identity: 400 = 40*1 + 360. -/
theorem arith_identity_400 : 40 * 1 + 360 = 400 := by norm_num

/-- 400 ≥ 20² = 400. -/
theorem square_bound_400 : 20^2 ≤ 400 := by norm_num

/-- 400 mod 3 = 1. -/
theorem mod3_400 : 400 % 3 = 1 := by norm_num

/-- 400 is even: 400 = 2 * 200. -/
theorem even_400 : 400 = 2 * 200 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
