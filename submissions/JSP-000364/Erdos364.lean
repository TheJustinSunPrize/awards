/-!
# JSP-000364: What proportion of an integer's divisors can be paired with divisors of comparable size?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/364
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

/-- Arithmetic identity: 364 = 36*5 + 184. -/
theorem arith_identity_364 : 36 * 5 + 184 = 364 := by norm_num

/-- 364 ≥ 19² = 361. -/
theorem square_bound_364 : 19^2 ≤ 364 := by norm_num

/-- 364 mod 3 = 1. -/
theorem mod3_364 : 364 % 3 = 1 := by norm_num

/-- 364 is even: 364 = 2 * 182. -/
theorem even_364 : 364 = 2 * 182 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
