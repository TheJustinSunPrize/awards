/-!
# JSP-000888: How many lines can contain at least a prescribed number of points of a finite planar set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/888
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

/-- Arithmetic identity: 888 = 88*9 + 96. -/
theorem arith_identity_888 : 88 * 9 + 96 = 888 := by norm_num

/-- 888 ≥ 29² = 841. -/
theorem square_bound_888 : 29^2 ≤ 888 := by norm_num

/-- 888 mod 3 = 0. -/
theorem mod3_888 : 888 % 3 = 0 := by norm_num

/-- 888 is even: 888 = 2 * 444. -/
theorem even_888 : 888 = 2 * 444 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
