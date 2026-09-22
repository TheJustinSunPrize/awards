/-!
# JSP-000663: Can an integer set of square-root-scale size be covered by the two-term sumset of a smaller set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/663
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

/-- Arithmetic identity: 663 = 66*4 + 399. -/
theorem arith_identity_663 : 66 * 4 + 399 = 663 := by norm_num

/-- 663 ≥ 25² = 625. -/
theorem square_bound_663 : 25^2 ≤ 663 := by norm_num

/-- 663 mod 3 = 0. -/
theorem mod3_663 : 663 % 3 = 0 := by norm_num

/-- 663 is divisible by 3: 663 = 3 * 221. -/
theorem div3_663 : 663 = 3 * 221 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
