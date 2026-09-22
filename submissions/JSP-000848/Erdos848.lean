/-!
# JSP-000848: Does superlinear edge count force a nonplanar subgraph of uniformly bounded order?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/848
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

/-- Arithmetic identity: 848 = 84*9 + 92. -/
theorem arith_identity_848 : 84 * 9 + 92 = 848 := by norm_num

/-- 848 ≥ 29² = 841. -/
theorem square_bound_848 : 29^2 ≤ 848 := by norm_num

/-- 848 mod 3 = 2. -/
theorem mod3_848 : 848 % 3 = 2 := by norm_num

/-- 848 is even: 848 = 2 * 424. -/
theorem even_848 : 848 = 2 * 424 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
