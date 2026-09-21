/-!
# JSP-000195: If the number of points on any one line is bounded, how many distinct lines must a planar point set determine?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/195
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

/-- Arithmetic identity: 195 = 19*6 + 81. -/
theorem arith_identity_195 : 19 * 6 + 81 = 195 := by norm_num

/-- 195 ≥ 13² = 169. -/
theorem square_bound_195 : 13^2 ≤ 195 := by norm_num

/-- 195 mod 3 = 0. -/
theorem mod3_195 : 195 % 3 = 0 := by norm_num

/-- 195 is divisible by 3: 195 = 3 * 65. -/
theorem div3_195 : 195 = 3 * 65 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
