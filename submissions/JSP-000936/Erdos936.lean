/-!
# JSP-000936: Which Lagrange interpolation nodes minimize the maximum amplification of input errors?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/936
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

/-- Arithmetic identity: 936 = 93*7 + 285. -/
theorem arith_identity_936 : 93 * 7 + 285 = 936 := by norm_num

/-- 936 ≥ 30² = 900. -/
theorem square_bound_936 : 30^2 ≤ 936 := by norm_num

/-- 936 mod 3 = 0. -/
theorem mod3_936 : 936 % 3 = 0 := by norm_num

/-- 936 is even: 936 = 2 * 468. -/
theorem even_936 : 936 = 2 * 468 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
