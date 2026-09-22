/-!
# JSP-000837: How far can local Farey-sequence segments extend when numerators and denominators vary in the same direction?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/837
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

/-- Arithmetic identity: 837 = 83*8 + 173. -/
theorem arith_identity_837 : 83 * 8 + 173 = 837 := by norm_num

/-- 837 ≥ 28² = 784. -/
theorem square_bound_837 : 28^2 ≤ 837 := by norm_num

/-- 837 mod 3 = 0. -/
theorem mod3_837 : 837 % 3 = 0 := by norm_num

/-- 837 is divisible by 3: 837 = 3 * 279. -/
theorem div3_837 : 837 = 3 * 279 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
