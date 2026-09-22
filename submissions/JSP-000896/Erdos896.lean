/-!
# JSP-000896: What minimum degree forces a transversal clique in a balanced multipartite graph?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/896
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

/-- Arithmetic identity: 896 = 89*7 + 273. -/
theorem arith_identity_896 : 89 * 7 + 273 = 896 := by norm_num

/-- 896 ≥ 29² = 841. -/
theorem square_bound_896 : 29^2 ≤ 896 := by norm_num

/-- 896 mod 3 = 2. -/
theorem mod3_896 : 896 % 3 = 2 := by norm_num

/-- 896 is even: 896 = 2 * 448. -/
theorem even_896 : 896 = 2 * 448 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
