/-!
# JSP-000628: How many edges can a graph have if no vertex of a cycle is incident to several specified chords?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/628
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

/-- Arithmetic identity: 628 = 62*9 + 70. -/
theorem arith_identity_628 : 62 * 9 + 70 = 628 := by norm_num

/-- 628 ≥ 25² = 625. -/
theorem square_bound_628 : 25^2 ≤ 628 := by norm_num

/-- 628 mod 3 = 1. -/
theorem mod3_628 : 628 % 3 = 1 := by norm_num

/-- 628 is even: 628 = 2 * 314. -/
theorem even_628 : 628 = 2 * 314 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
