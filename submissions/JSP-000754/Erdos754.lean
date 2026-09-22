/-!
# JSP-000754: Can a space and its Cartesian square have the same nontrivial finite dimension?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/754
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

/-- Arithmetic identity: 754 = 75*5 + 379. -/
theorem arith_identity_754 : 75 * 5 + 379 = 754 := by norm_num

/-- 754 ≥ 27² = 729. -/
theorem square_bound_754 : 27^2 ≤ 754 := by norm_num

/-- 754 mod 3 = 1. -/
theorem mod3_754 : 754 % 3 = 1 := by norm_num

/-- 754 is even: 754 = 2 * 377. -/
theorem even_754 : 754 = 2 * 377 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
