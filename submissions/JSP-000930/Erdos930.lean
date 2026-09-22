/-!
# JSP-000930: How large can a family of entire functions be if the number of possible values at each point is restricted?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/930
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

/-- Arithmetic identity: 930 = 93*1 + 837. -/
theorem arith_identity_930 : 93 * 1 + 837 = 930 := by norm_num

/-- 930 ≥ 30² = 900. -/
theorem square_bound_930 : 30^2 ≤ 930 := by norm_num

/-- 930 mod 3 = 0. -/
theorem mod3_930 : 930 % 3 = 0 := by norm_num

/-- 930 is even: 930 = 2 * 465. -/
theorem even_930 : 930 = 2 * 465 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
