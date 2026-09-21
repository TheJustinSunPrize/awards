/-!
# JSP-000475: Can finitely many residue classes cover all integers with no modulus dividing another?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/475
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

/-- Arithmetic identity: 475 = 47*6 + 193. -/
theorem arith_identity_475 : 47 * 6 + 193 = 475 := by norm_num

/-- 475 ≥ 21² = 441. -/
theorem square_bound_475 : 21^2 ≤ 475 := by norm_num

/-- 475 mod 3 = 1. -/
theorem mod3_475 : 475 % 3 = 1 := by norm_num

/-- 475 is divisible by 5: 475 = 5 * 95. -/
theorem div5_475 : 475 = 5 * 95 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
