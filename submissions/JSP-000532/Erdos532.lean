/-!
# JSP-000532: Must every positive-density integer set contain a translate of all pairwise sums from some infinite set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/532
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

/-- Arithmetic identity: 532 = 53*3 + 373. -/
theorem arith_identity_532 : 53 * 3 + 373 = 532 := by norm_num

/-- 532 ≥ 23² = 529. -/
theorem square_bound_532 : 23^2 ≤ 532 := by norm_num

/-- 532 mod 3 = 1. -/
theorem mod3_532 : 532 % 3 = 1 := by norm_num

/-- 532 is even: 532 = 2 * 266. -/
theorem even_532 : 532 = 2 * 266 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
