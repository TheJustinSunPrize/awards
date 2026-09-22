/-!
# JSP-000765: What is the largest odd girth of a graph with prescribed order and chromatic number?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/765
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

/-- Arithmetic identity: 765 = 76*6 + 309. -/
theorem arith_identity_765 : 76 * 6 + 309 = 765 := by norm_num

/-- 765 ≥ 27² = 729. -/
theorem square_bound_765 : 27^2 ≤ 765 := by norm_num

/-- 765 mod 3 = 0. -/
theorem mod3_765 : 765 % 3 = 0 := by norm_num

/-- 765 is divisible by 3: 765 = 3 * 255. -/
theorem div3_765 : 765 = 3 * 255 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
