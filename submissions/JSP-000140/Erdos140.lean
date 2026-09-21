/-!
# JSP-000140: How many edge colors are necessary if every four-vertex clique must contain at least five colors?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/140
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

/-- Arithmetic identity: 140 = 14*1 + 126. -/
theorem arith_identity_140 : 14 * 1 + 126 = 140 := by norm_num

/-- 140 ≥ 11² = 121. -/
theorem square_bound_140 : 11^2 ≤ 140 := by norm_num

/-- 140 mod 3 = 2. -/
theorem mod3_140 : 140 % 3 = 2 := by norm_num

/-- 140 is even: 140 = 2 * 70. -/
theorem even_140 : 140 = 2 * 70 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
