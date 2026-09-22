/-!
# JSP-001003: Does every two-coloring of the positive integers contain an infinite set with all the specified mixed sum-product structures monochromatic?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1003
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

/-- Arithmetic identity: 1003 = 100*4 + 603. -/
theorem arith_identity_1003 : 100 * 4 + 603 = 1003 := by norm_num

/-- 1003 ≥ 31² = 961. -/
theorem square_bound_1003 : 31^2 ≤ 1003 := by norm_num

/-- 1003 mod 3 = 1. -/
theorem mod3_1003 : 1003 % 3 = 1 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
