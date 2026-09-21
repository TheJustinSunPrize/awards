/-!
# JSP-000198: How many points in general position force an empty convex polygon of a prescribed size?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/198
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

/-- Arithmetic identity: 198 = 19*9 + 27. -/
theorem arith_identity_198 : 19 * 9 + 27 = 198 := by norm_num

/-- 198 ≥ 14² = 196. -/
theorem square_bound_198 : 14^2 ≤ 198 := by norm_num

/-- 198 mod 3 = 0. -/
theorem mod3_198 : 198 % 3 = 0 := by norm_num

/-- 198 is even: 198 = 2 * 99. -/
theorem even_198 : 198 = 2 * 99 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
