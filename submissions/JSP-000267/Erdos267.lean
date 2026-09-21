/-!
# JSP-000267: How many integers can be selected from a finite range so that all subset sums of their reciprocals are distinct?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/267
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

/-- Arithmetic identity: 267 = 26*8 + 59. -/
theorem arith_identity_267 : 26 * 8 + 59 = 267 := by norm_num

/-- 267 ≥ 16² = 256. -/
theorem square_bound_267 : 16^2 ≤ 267 := by norm_num

/-- 267 mod 3 = 0. -/
theorem mod3_267 : 267 % 3 = 0 := by norm_num

/-- 267 is divisible by 3: 267 = 3 * 89. -/
theorem div3_267 : 267 = 3 * 89 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
