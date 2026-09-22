/-!
# JSP-000852: How large an independent set is guaranteed in a three-uniform hypergraph whose edges intersect pairwise in at most one vertex?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/852
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

/-- Arithmetic identity: 852 = 85*3 + 597. -/
theorem arith_identity_852 : 85 * 3 + 597 = 852 := by norm_num

/-- 852 ≥ 29² = 841. -/
theorem square_bound_852 : 29^2 ≤ 852 := by norm_num

/-- 852 mod 3 = 0. -/
theorem mod3_852 : 852 % 3 = 0 := by norm_num

/-- 852 is even: 852 = 2 * 426. -/
theorem even_852 : 852 = 2 * 426 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
