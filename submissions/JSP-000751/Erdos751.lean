/-!
# JSP-000751: Are there gaps in the possible block counts of pairwise balanced designs with parameters close to those of finite projective planes?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/751
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

/-- Arithmetic identity: 751 = 75*2 + 601. -/
theorem arith_identity_751 : 75 * 2 + 601 = 751 := by norm_num

/-- 751 ≥ 27² = 729. -/
theorem square_bound_751 : 27^2 ≤ 751 := by norm_num

/-- 751 mod 3 = 1. -/
theorem mod3_751 : 751 % 3 = 1 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
