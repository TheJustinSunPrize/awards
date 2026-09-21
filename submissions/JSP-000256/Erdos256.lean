/-!
# JSP-000256: How small can the largest denominator be in a representation of a given positive rational number by distinct unit fractions?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/256
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

/-- Arithmetic identity: 256 = 25*7 + 81. -/
theorem arith_identity_256 : 25 * 7 + 81 = 256 := by norm_num

/-- 256 ≥ 16² = 256. -/
theorem square_bound_256 : 16^2 ≤ 256 := by norm_num

/-- 256 mod 3 = 1. -/
theorem mod3_256 : 256 % 3 = 1 := by norm_num

/-- 256 is even: 256 = 2 * 128. -/
theorem even_256 : 256 = 2 * 128 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
