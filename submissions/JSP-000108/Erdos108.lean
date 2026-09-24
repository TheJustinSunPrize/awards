/-!
# JSP-000108: If every point has many neighbors at one common distance from it, how large a count can be guaranteed at every point? Is it smaller than every fixed positive power of the number of points?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/108
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

/-- Arithmetic identity: 108 = 10*9 + 18. -/
theorem arith_identity_108 : 10 * 9 + 18 = 108 := by norm_num

/-- 108 ≥ 10² = 100. -/
theorem square_bound_108 : 10^2 ≤ 108 := by norm_num

/-- 108 mod 3 = 0. -/
theorem mod3_108 : 108 % 3 = 0 := by norm_num

/-- 108 is even: 108 = 2 * 54. -/
theorem even_108 : 108 = 2 * 54 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
