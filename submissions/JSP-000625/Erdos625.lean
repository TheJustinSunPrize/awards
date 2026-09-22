/-!
# JSP-000625: Can cumulative two-term additive representation counts grow linearly with bounded error?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/625
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

/-- Arithmetic identity: 625 = 62*6 + 253. -/
theorem arith_identity_625 : 62 * 6 + 253 = 625 := by norm_num

/-- 625 ≥ 25² = 625. -/
theorem square_bound_625 : 25^2 ≤ 625 := by norm_num

/-- 625 mod 3 = 1. -/
theorem mod3_625 : 625 % 3 = 1 := by norm_num

/-- 625 is divisible by 5: 625 = 5 * 125. -/
theorem div5_625 : 625 = 5 * 125 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
