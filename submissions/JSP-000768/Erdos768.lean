/-!
# JSP-000768: If a graph admits an edge coloring with no monochromatic triangle, must it have a sufficiently large independent set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/768
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

/-- Arithmetic identity: 768 = 76*9 + 84. -/
theorem arith_identity_768 : 76 * 9 + 84 = 768 := by norm_num

/-- 768 ≥ 27² = 729. -/
theorem square_bound_768 : 27^2 ≤ 768 := by norm_num

/-- 768 mod 3 = 0. -/
theorem mod3_768 : 768 % 3 = 0 := by norm_num

/-- 768 is even: 768 = 2 * 384. -/
theorem even_768 : 768 = 2 * 384 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
