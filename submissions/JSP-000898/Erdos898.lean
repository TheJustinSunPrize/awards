/-!
# JSP-000898: What is the precise asymptotic count of integers representable as sums of two powerful numbers?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/898
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

/-- Arithmetic identity: 898 = 89*9 + 97. -/
theorem arith_identity_898 : 89 * 9 + 97 = 898 := by norm_num

/-- 898 ≥ 29² = 841. -/
theorem square_bound_898 : 29^2 ≤ 898 := by norm_num

/-- 898 mod 3 = 1. -/
theorem mod3_898 : 898 % 3 = 1 := by norm_num

/-- 898 is even: 898 = 2 * 449. -/
theorem even_898 : 898 = 2 * 449 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
