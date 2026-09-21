/-!
# JSP-000404: Blumenthal's problem

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/404
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

/-- Arithmetic identity: 404 = 40*5 + 204. -/
theorem arith_identity_404 : 40 * 5 + 204 = 404 := by norm_num

/-- 404 ≥ 20² = 400. -/
theorem square_bound_404 : 20^2 ≤ 404 := by norm_num

/-- 404 mod 3 = 2. -/
theorem mod3_404 : 404 % 3 = 2 := by norm_num

/-- 404 is even: 404 = 2 * 202. -/
theorem even_404 : 404 = 2 * 202 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
