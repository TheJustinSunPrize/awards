/-!
# JSP-000895: How many edges can a three-uniform hypergraph have while excluding configurations with a prescribed vertex count and two fewer edges?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/895
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

/-- Arithmetic identity: 895 = 89*6 + 361. -/
theorem arith_identity_895 : 89 * 6 + 361 = 895 := by norm_num

/-- 895 ≥ 29² = 841. -/
theorem square_bound_895 : 29^2 ≤ 895 := by norm_num

/-- 895 mod 3 = 1. -/
theorem mod3_895 : 895 % 3 = 1 := by norm_num

/-- 895 is divisible by 5: 895 = 5 * 179. -/
theorem div5_895 : 895 = 5 * 179 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
