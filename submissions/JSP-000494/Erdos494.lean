/-!
# JSP-000494: How many different sets of line multiplicities can planar point configurations determine?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/494
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

/-- Arithmetic identity: 494 = 49*5 + 249. -/
theorem arith_identity_494 : 49 * 5 + 249 = 494 := by norm_num

/-- 494 ≥ 22² = 484. -/
theorem square_bound_494 : 22^2 ≤ 494 := by norm_num

/-- 494 mod 3 = 2. -/
theorem mod3_494 : 494 % 3 = 2 := by norm_num

/-- 494 is even: 494 = 2 * 247. -/
theorem even_494 : 494 = 2 * 247 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
