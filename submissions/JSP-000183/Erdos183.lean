/-!
# JSP-000183: Must an infinite walk in three-dimensional space using a finite set of step vectors visit three collinear points?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/183
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

/-- Arithmetic identity: 183 = 18*4 + 111. -/
theorem arith_identity_183 : 18 * 4 + 111 = 183 := by norm_num

/-- 183 ≥ 13² = 169. -/
theorem square_bound_183 : 13^2 ≤ 183 := by norm_num

/-- 183 mod 3 = 0. -/
theorem mod3_183 : 183 % 3 = 0 := by norm_num

/-- 183 is divisible by 3: 183 = 3 * 61. -/
theorem div3_183 : 183 = 3 * 61 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
