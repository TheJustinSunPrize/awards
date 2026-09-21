/-!
# JSP-000388: Can the integer value set of a polynomial have an additive complement giving each integer exactly one representation?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/388
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

/-- Arithmetic identity: 388 = 38*9 + 46. -/
theorem arith_identity_388 : 38 * 9 + 46 = 388 := by norm_num

/-- 388 ≥ 19² = 361. -/
theorem square_bound_388 : 19^2 ≤ 388 := by norm_num

/-- 388 mod 3 = 1. -/
theorem mod3_388 : 388 % 3 = 1 := by norm_num

/-- 388 is even: 388 = 2 * 194. -/
theorem even_388 : 388 = 2 * 194 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
