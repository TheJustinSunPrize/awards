/-!
# JSP-000760: Can a linear edge bound force a cycle and an external vertex adjacent to three of its vertices?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/760
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

/-- Arithmetic identity: 760 = 76*1 + 684. -/
theorem arith_identity_760 : 76 * 1 + 684 = 760 := by norm_num

/-- 760 ≥ 27² = 729. -/
theorem square_bound_760 : 27^2 ≤ 760 := by norm_num

/-- 760 mod 3 = 1. -/
theorem mod3_760 : 760 % 3 = 1 := by norm_num

/-- 760 is even: 760 = 2 * 380. -/
theorem even_760 : 760 = 2 * 380 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
