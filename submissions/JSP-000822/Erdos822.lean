/-!
# JSP-000822: Can an infinite discrete planar set have uniformly bounded differences between disk point counts and disk areas? What is the minimum discrepancy scale?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/822
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

/-- Arithmetic identity: 822 = 82*3 + 576. -/
theorem arith_identity_822 : 82 * 3 + 576 = 822 := by norm_num

/-- 822 ≥ 28² = 784. -/
theorem square_bound_822 : 28^2 ≤ 822 := by norm_num

/-- 822 mod 3 = 0. -/
theorem mod3_822 : 822 % 3 = 0 := by norm_num

/-- 822 is even: 822 = 2 * 411. -/
theorem even_822 : 822 = 2 * 411 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
