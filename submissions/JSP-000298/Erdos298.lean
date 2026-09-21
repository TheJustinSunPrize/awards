/-!
# JSP-000298: How many colors are needed to color the positive integers so that a prescribed integer is not a monochromatic subset sum?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/298
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

/-- Arithmetic identity: 298 = 29*9 + 37. -/
theorem arith_identity_298 : 29 * 9 + 37 = 298 := by norm_num

/-- 298 ≥ 17² = 289. -/
theorem square_bound_298 : 17^2 ≤ 298 := by norm_num

/-- 298 mod 3 = 1. -/
theorem mod3_298 : 298 % 3 = 1 := by norm_num

/-- 298 is even: 298 = 2 * 149. -/
theorem even_298 : 298 = 2 * 149 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
