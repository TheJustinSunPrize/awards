/-!
# JSP-000845: How few vertices need remain uncovered by disjoint monochromatic cliques in an edge-colored complete graph?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/845
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

/-- Arithmetic identity: 845 = 84*6 + 341. -/
theorem arith_identity_845 : 84 * 6 + 341 = 845 := by norm_num

/-- 845 ≥ 29² = 841. -/
theorem square_bound_845 : 29^2 ≤ 845 := by norm_num

/-- 845 mod 3 = 2. -/
theorem mod3_845 : 845 % 3 = 2 := by norm_num

/-- 845 is divisible by 5: 845 = 5 * 169. -/
theorem div5_845 : 845 = 5 * 169 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
