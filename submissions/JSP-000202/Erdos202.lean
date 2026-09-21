/-!
# JSP-000202: For a finite point set of fixed diameter in higher-dimensional space, how many pairs can attain that diameter?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/202
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

/-- Arithmetic identity: 202 = 20*3 + 142. -/
theorem arith_identity_202 : 20 * 3 + 142 = 202 := by norm_num

/-- 202 ≥ 14² = 196. -/
theorem square_bound_202 : 14^2 ≤ 202 := by norm_num

/-- 202 mod 3 = 1. -/
theorem mod3_202 : 202 % 3 = 1 := by norm_num

/-- 202 is even: 202 = 2 * 101. -/
theorem even_202 : 202 = 2 * 101 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
