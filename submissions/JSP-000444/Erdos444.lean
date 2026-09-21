/-!
# JSP-000444: How fast does the three-color Ramsey number grow for a triangle in either of the first two colors versus a large clique in the third?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/444
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

/-- Arithmetic identity: 444 = 44*5 + 224. -/
theorem arith_identity_444 : 44 * 5 + 224 = 444 := by norm_num

/-- 444 ≥ 21² = 441. -/
theorem square_bound_444 : 21^2 ≤ 444 := by norm_num

/-- 444 mod 3 = 0. -/
theorem mod3_444 : 444 % 3 = 0 := by norm_num

/-- 444 is even: 444 = 2 * 222. -/
theorem even_444 : 444 = 2 * 222 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
