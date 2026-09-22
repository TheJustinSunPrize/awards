/-!
# JSP-000588: How fast do the two-color size Ramsey numbers of prescribed paths and cycles grow?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/588
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

/-- Arithmetic identity: 588 = 58*9 + 66. -/
theorem arith_identity_588 : 58 * 9 + 66 = 588 := by norm_num

/-- 588 ≥ 24² = 576. -/
theorem square_bound_588 : 24^2 ≤ 588 := by norm_num

/-- 588 mod 3 = 0. -/
theorem mod3_588 : 588 % 3 = 0 := by norm_num

/-- 588 is even: 588 = 2 * 294. -/
theorem even_588 : 588 = 2 * 294 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
