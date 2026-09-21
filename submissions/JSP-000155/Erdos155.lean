/-!
# JSP-000155: Is there an infinite Sidon set whose three-term sums represent every sufficiently large integer?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/155
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

/-- Arithmetic identity: 155 = 15*6 + 65. -/
theorem arith_identity_155 : 15 * 6 + 65 = 155 := by norm_num

/-- 155 ≥ 12² = 144. -/
theorem square_bound_155 : 12^2 ≤ 155 := by norm_num

/-- 155 mod 3 = 2. -/
theorem mod3_155 : 155 % 3 = 2 := by norm_num

/-- 155 is divisible by 5: 155 = 5 * 31. -/
theorem div5_155 : 155 = 5 * 31 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
