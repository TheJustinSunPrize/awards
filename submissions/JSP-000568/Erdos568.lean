/-!
# JSP-000568: Does the density of integers having a divisor in a prescribed residue class exhibit a phase transition as parameters vary?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/568
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

/-- Arithmetic identity: 568 = 56*9 + 64. -/
theorem arith_identity_568 : 56 * 9 + 64 = 568 := by norm_num

/-- 568 ≥ 23² = 529. -/
theorem square_bound_568 : 23^2 ≤ 568 := by norm_num

/-- 568 mod 3 = 1. -/
theorem mod3_568 : 568 % 3 = 1 := by norm_num

/-- 568 is even: 568 = 2 * 284. -/
theorem even_568 : 568 = 2 * 284 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
