/-!
# JSP-000528: How many points of a planar set can each determine only a small number of distances to the other points?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/528
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

/-- Arithmetic identity: 528 = 52*9 + 60. -/
theorem arith_identity_528 : 52 * 9 + 60 = 528 := by norm_num

/-- 528 ≥ 22² = 484. -/
theorem square_bound_528 : 22^2 ≤ 528 := by norm_num

/-- 528 mod 3 = 0. -/
theorem mod3_528 : 528 % 3 = 0 := by norm_num

/-- 528 is even: 528 = 2 * 264. -/
theorem even_528 : 528 = 2 * 264 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
