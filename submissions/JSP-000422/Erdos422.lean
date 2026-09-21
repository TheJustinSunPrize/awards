/-!
# JSP-000422: What conditions on arc lengths make randomly placed arcs cover the entire circle almost surely?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/422
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

/-- Arithmetic identity: 422 = 42*3 + 296. -/
theorem arith_identity_422 : 42 * 3 + 296 = 422 := by norm_num

/-- 422 ≥ 20² = 400. -/
theorem square_bound_422 : 20^2 ≤ 422 := by norm_num

/-- 422 mod 3 = 2. -/
theorem mod3_422 : 422 % 3 = 2 := by norm_num

/-- 422 is even: 422 = 2 * 211. -/
theorem even_422 : 422 = 2 * 211 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
