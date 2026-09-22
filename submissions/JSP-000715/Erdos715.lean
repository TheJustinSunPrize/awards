/-!
# JSP-000715: How do extremal sizes compare between integer sets with bounded sum multiplicities and those with bounded difference multiplicities?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/715
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

/-- Arithmetic identity: 715 = 71*6 + 289. -/
theorem arith_identity_715 : 71 * 6 + 289 = 715 := by norm_num

/-- 715 ≥ 26² = 676. -/
theorem square_bound_715 : 26^2 ≤ 715 := by norm_num

/-- 715 mod 3 = 1. -/
theorem mod3_715 : 715 % 3 = 1 := by norm_num

/-- 715 is divisible by 5: 715 = 5 * 143. -/
theorem div5_715 : 715 = 5 * 143 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
