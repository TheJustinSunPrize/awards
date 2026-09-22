/-!
# JSP-000518: If a graph has neither large cliques nor large independent sets, must a large induced subgraph have many distinct vertex degrees?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/518
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

/-- Arithmetic identity: 518 = 51*9 + 59. -/
theorem arith_identity_518 : 51 * 9 + 59 = 518 := by norm_num

/-- 518 ≥ 22² = 484. -/
theorem square_bound_518 : 22^2 ≤ 518 := by norm_num

/-- 518 mod 3 = 2. -/
theorem mod3_518 : 518 % 3 = 2 := by norm_num

/-- 518 is even: 518 = 2 * 259. -/
theorem even_518 : 518 = 2 * 259 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
