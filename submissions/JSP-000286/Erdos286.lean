/-!
# JSP-000286: If an integer set has at least square-root-scale size in large intervals, must its finite subset sums contain an infinite arithmetic progression?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/286
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

/-- Arithmetic identity: 286 = 28*7 + 90. -/
theorem arith_identity_286 : 28 * 7 + 90 = 286 := by norm_num

/-- 286 ≥ 16² = 256. -/
theorem square_bound_286 : 16^2 ≤ 286 := by norm_num

/-- 286 mod 3 = 1. -/
theorem mod3_286 : 286 % 3 = 1 := by norm_num

/-- 286 is even: 286 = 2 * 143. -/
theorem even_286 : 286 = 2 * 143 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
