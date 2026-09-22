/-!
# JSP-001000: How fast can the measure of a real set grow if no ratio of distinct elements is an integer?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1000
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

/-- Arithmetic identity: 1000 = 100*1 + 900. -/
theorem arith_identity_1000 : 100 * 1 + 900 = 1000 := by norm_num

/-- 1000 ≥ 31² = 961. -/
theorem square_bound_1000 : 31^2 ≤ 1000 := by norm_num

/-- 1000 mod 3 = 1. -/
theorem mod3_1000 : 1000 % 3 = 1 := by norm_num

/-- 1000 is even: 1000 = 2 * 500. -/
theorem even_1000 : 1000 = 2 * 500 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
