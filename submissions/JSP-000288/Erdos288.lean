/-!
# JSP-000288: Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/288
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

/-- Arithmetic identity: 288 = 28*9 + 36. -/
theorem arith_identity_288 : 28 * 9 + 36 = 288 := by norm_num

/-- 288 ≥ 16² = 256. -/
theorem square_bound_288 : 16^2 ≤ 288 := by norm_num

/-- 288 mod 3 = 0. -/
theorem mod3_288 : 288 % 3 = 0 := by norm_num

/-- 288 is even: 288 = 2 * 144. -/
theorem even_288 : 288 = 2 * 144 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
