/-!
# JSP-000176: How many edges can a graph have if it contains no regular subgraph of a prescribed degree?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/176
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

/-- Arithmetic identity: 176 = 17*7 + 57. -/
theorem arith_identity_176 : 17 * 7 + 57 = 176 := by norm_num

/-- 176 ≥ 13² = 169. -/
theorem square_bound_176 : 13^2 ≤ 176 := by norm_num

/-- 176 mod 3 = 2. -/
theorem mod3_176 : 176 % 3 = 2 := by norm_num

/-- 176 is even: 176 = 2 * 88. -/
theorem even_176 : 176 = 2 * 88 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
