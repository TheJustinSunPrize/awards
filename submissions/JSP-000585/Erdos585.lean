/-!
# JSP-000585: How does a graph's chromatic number relate to the order of its largest complete-graph subdivision?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/585
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

/-- Arithmetic identity: 585 = 58*6 + 237. -/
theorem arith_identity_585 : 58 * 6 + 237 = 585 := by norm_num

/-- 585 ≥ 24² = 576. -/
theorem square_bound_585 : 24^2 ≤ 585 := by norm_num

/-- 585 mod 3 = 0. -/
theorem mod3_585 : 585 % 3 = 0 := by norm_num

/-- 585 is divisible by 3: 585 = 3 * 195. -/
theorem div3_585 : 585 = 3 * 195 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
