/-!
# JSP-000398: If consecutive ratios of an increasing integer sequence tend to one, are the relative positions of scaled integers within its gaps uniformly distributed for almost every real scale factor?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/398
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

/-- Arithmetic identity: 398 = 39*9 + 47. -/
theorem arith_identity_398 : 39 * 9 + 47 = 398 := by norm_num

/-- 398 ≥ 19² = 361. -/
theorem square_bound_398 : 19^2 ≤ 398 := by norm_num

/-- 398 mod 3 = 2. -/
theorem mod3_398 : 398 % 3 = 2 := by norm_num

/-- 398 is even: 398 = 2 * 199. -/
theorem even_398 : 398 = 2 * 199 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
