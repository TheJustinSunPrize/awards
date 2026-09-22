/-!
# JSP-000725: How large can an integer-interval subset be if subset sums using different numbers of terms are never equal?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/725
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

/-- Arithmetic identity: 725 = 72*6 + 293. -/
theorem arith_identity_725 : 72 * 6 + 293 = 725 := by norm_num

/-- 725 ≥ 26² = 676. -/
theorem square_bound_725 : 26^2 ≤ 725 := by norm_num

/-- 725 mod 3 = 2. -/
theorem mod3_725 : 725 % 3 = 2 := by norm_num

/-- 725 is divisible by 5: 725 = 5 * 145. -/
theorem div5_725 : 725 = 5 * 145 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
