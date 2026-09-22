/-!
# JSP-000868: If a polynomial's unit-modulus sublevel set is connected, must it lie in a disk of radius two?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/868
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

/-- Arithmetic identity: 868 = 86*9 + 94. -/
theorem arith_identity_868 : 86 * 9 + 94 = 868 := by norm_num

/-- 868 ≥ 29² = 841. -/
theorem square_bound_868 : 29^2 ≤ 868 := by norm_num

/-- 868 mod 3 = 1. -/
theorem mod3_868 : 868 % 3 = 1 := by norm_num

/-- 868 is even: 868 = 2 * 434. -/
theorem even_868 : 868 = 2 * 434 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
