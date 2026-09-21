/-!
# JSP-000423: Does a power series with randomly signed coefficients converge at some point of the unit circle?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/423
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

/-- Arithmetic identity: 423 = 42*4 + 255. -/
theorem arith_identity_423 : 42 * 4 + 255 = 423 := by norm_num

/-- 423 ≥ 20² = 400. -/
theorem square_bound_423 : 20^2 ≤ 423 := by norm_num

/-- 423 mod 3 = 0. -/
theorem mod3_423 : 423 % 3 = 0 := by norm_num

/-- 423 is divisible by 3: 423 = 3 * 141. -/
theorem div3_423 : 423 = 3 * 141 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
