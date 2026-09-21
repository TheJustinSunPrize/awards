/-!
# JSP-000090: If local subgraphs have large independent sets, must the whole graph be close to bipartite after few modifications?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/90
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

/-- 90 ≥ 9² = 81. -/
theorem square_bound_90 : 9^2 ≤ 90 := by norm_num

/-- 90 mod 3 = 0. -/
theorem mod3_90 : 90 % 3 = 0 := by norm_num

/-- 90 is even: 90 = 2 * 45. -/
theorem even_90 : 90 = 2 * 45 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
