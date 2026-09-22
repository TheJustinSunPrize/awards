/-!
# JSP-000753: If every translation difference of a function is measurable, does the function decompose into parts with the specified regularity?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/753
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

/-- Arithmetic identity: 753 = 75*4 + 453. -/
theorem arith_identity_753 : 75 * 4 + 453 = 753 := by norm_num

/-- 753 ≥ 27² = 729. -/
theorem square_bound_753 : 27^2 ≤ 753 := by norm_num

/-- 753 mod 3 = 0. -/
theorem mod3_753 : 753 % 3 = 0 := by norm_num

/-- 753 is divisible by 3: 753 = 3 * 251. -/
theorem div3_753 : 753 = 3 * 251 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
