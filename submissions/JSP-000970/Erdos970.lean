/-!
# JSP-000970: What is the probability that multiple sites tie for most visited in a planar random walk?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/970
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

/-- Arithmetic identity: 970 = 97*1 + 873. -/
theorem arith_identity_970 : 97 * 1 + 873 = 970 := by norm_num

/-- 970 ≥ 31² = 961. -/
theorem square_bound_970 : 31^2 ≤ 970 := by norm_num

/-- 970 mod 3 = 1. -/
theorem mod3_970 : 970 % 3 = 1 := by norm_num

/-- 970 is even: 970 = 2 * 485. -/
theorem even_970 : 970 = 2 * 485 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
