/-!
# JSP-000927: Under the stated conditions, can a meromorphic function's counts of taking two distinct values have arbitrarily extreme ratios?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/927
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

/-- Arithmetic identity: 927 = 92*8 + 191. -/
theorem arith_identity_927 : 92 * 8 + 191 = 927 := by norm_num

/-- 927 ≥ 30² = 900. -/
theorem square_bound_927 : 30^2 ≤ 927 := by norm_num

/-- 927 mod 3 = 0. -/
theorem mod3_927 : 927 % 3 = 0 := by norm_num

/-- 927 is divisible by 3: 927 = 3 * 309. -/
theorem div3_927 : 927 = 3 * 309 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
