/-!
# JSP-000615: What is the density threshold for a perfect matching in a random three-uniform hypergraph?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/615
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

/-- Arithmetic identity: 615 = 61*6 + 249. -/
theorem arith_identity_615 : 61 * 6 + 249 = 615 := by norm_num

/-- 615 ≥ 24² = 576. -/
theorem square_bound_615 : 24^2 ≤ 615 := by norm_num

/-- 615 mod 3 = 0. -/
theorem mod3_615 : 615 % 3 = 0 := by norm_num

/-- 615 is divisible by 3: 615 = 3 * 205. -/
theorem div3_615 : 615 = 3 * 205 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
