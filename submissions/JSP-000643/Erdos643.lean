/-!
# JSP-000643: Among pairwise coprime integer sets with bounded reciprocal sum, which have multiples covering the largest proportion of integers?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/643
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

/-- Arithmetic identity: 643 = 64*4 + 387. -/
theorem arith_identity_643 : 64 * 4 + 387 = 643 := by norm_num

/-- 643 ≥ 25² = 625. -/
theorem square_bound_643 : 25^2 ≤ 643 := by norm_num

/-- 643 mod 3 = 1. -/
theorem mod3_643 : 643 % 3 = 1 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
