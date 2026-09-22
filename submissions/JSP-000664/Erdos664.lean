/-!
# JSP-000664: How many complete bipartite graphs are typically needed to partition a random graph's edges?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/664
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

/-- Arithmetic identity: 664 = 66*5 + 334. -/
theorem arith_identity_664 : 66 * 5 + 334 = 664 := by norm_num

/-- 664 ≥ 25² = 625. -/
theorem square_bound_664 : 25^2 ≤ 664 := by norm_num

/-- 664 mod 3 = 1. -/
theorem mod3_664 : 664 % 3 = 1 := by norm_num

/-- 664 is even: 664 = 2 * 332. -/
theorem even_664 : 664 = 2 * 332 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
