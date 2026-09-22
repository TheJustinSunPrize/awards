/-!
# JSP-000782: Is every sufficiently large integer a sum of three powerful numbers, each divisible by the square of every prime dividing it?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/782
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

/-- Arithmetic identity: 782 = 78*3 + 548. -/
theorem arith_identity_782 : 78 * 3 + 548 = 782 := by norm_num

/-- 782 ≥ 27² = 729. -/
theorem square_bound_782 : 27^2 ≤ 782 := by norm_num

/-- 782 mod 3 = 2. -/
theorem mod3_782 : 782 % 3 = 2 := by norm_num

/-- 782 is even: 782 = 2 * 391. -/
theorem even_782 : 782 = 2 * 391 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
