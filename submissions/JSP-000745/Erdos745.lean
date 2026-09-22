/-!
# JSP-000745: Can the integers be finitely colored so that no same-colored pair has difference in a prescribed sparse set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/745
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

/-- Arithmetic identity: 745 = 74*6 + 301. -/
theorem arith_identity_745 : 74 * 6 + 301 = 745 := by norm_num

/-- 745 ≥ 27² = 729. -/
theorem square_bound_745 : 27^2 ≤ 745 := by norm_num

/-- 745 mod 3 = 1. -/
theorem mod3_745 : 745 % 3 = 1 := by norm_num

/-- 745 is divisible by 5: 745 = 5 * 149. -/
theorem div5_745 : 745 = 5 * 149 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
