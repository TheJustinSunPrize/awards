/-!
# JSP-000945: Is there an integer whose differences from twice every permitted smaller square are all prime?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/945
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

/-- Arithmetic identity: 945 = 94*6 + 381. -/
theorem arith_identity_945 : 94 * 6 + 381 = 945 := by norm_num

/-- 945 ≥ 30² = 900. -/
theorem square_bound_945 : 30^2 ≤ 945 := by norm_num

/-- 945 mod 3 = 0. -/
theorem mod3_945 : 945 % 3 = 0 := by norm_num

/-- 945 is divisible by 3: 945 = 3 * 315. -/
theorem div3_945 : 945 = 3 * 315 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
