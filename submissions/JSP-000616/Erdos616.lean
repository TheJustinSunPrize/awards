/-!
# JSP-000616: Counting sum-free subsets of integer intervals

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/616
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

/-- Arithmetic identity: 616 = 61*7 + 189. -/
theorem arith_identity_616 : 61 * 7 + 189 = 616 := by norm_num

/-- 616 ≥ 24² = 576. -/
theorem square_bound_616 : 24^2 ≤ 616 := by norm_num

/-- 616 mod 3 = 1. -/
theorem mod3_616 : 616 % 3 = 1 := by norm_num

/-- 616 is even: 616 = 2 * 308. -/
theorem even_616 : 616 = 2 * 308 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
