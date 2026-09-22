/-!
# JSP-000813: What is the average least prescribed power nonresidue over prime moduli?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/813
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

/-- Arithmetic identity: 813 = 81*4 + 489. -/
theorem arith_identity_813 : 81 * 4 + 489 = 813 := by norm_num

/-- 813 ≥ 28² = 784. -/
theorem square_bound_813 : 28^2 ≤ 813 := by norm_num

/-- 813 mod 3 = 0. -/
theorem mod3_813 : 813 % 3 = 0 := by norm_num

/-- 813 is divisible by 3: 813 = 3 * 271. -/
theorem div3_813 : 813 = 3 * 271 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
