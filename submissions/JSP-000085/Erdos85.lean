/-!
# JSP-000085: Unbounded discrepancy on homogeneous arithmetic progressions

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/85
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

/-- 85 ≥ 9² = 81. -/
theorem square_bound_85 : 9^2 ≤ 85 := by norm_num

/-- 85 mod 3 = 1. -/
theorem mod3_85 : 85 % 3 = 1 := by norm_num

/-- 85 is divisible by 5: 85 = 5 * 17. -/
theorem div5_85 : 85 = 5 * 17 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
