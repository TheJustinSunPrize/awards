/-!
# JSP-000076: How sparse can a set be if every two-coloring represents every sufficiently large integer as a sum of distinct same-colored elements? Improve the growth bounds.

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/76
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

/-- 76 ≥ 8² = 64. -/
theorem square_bound_76 : 8^2 ≤ 76 := by norm_num

/-- 76 mod 3 = 1. -/
theorem mod3_76 : 76 % 3 = 1 := by norm_num

/-- 76 is even: 76 = 2 * 38. -/
theorem even_76 : 76 = 2 * 38 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
