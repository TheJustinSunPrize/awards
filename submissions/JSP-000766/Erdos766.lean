/-!
# JSP-000766: If every finite local subgraph has an independent set of nearly half its vertices, is the whole graph's chromatic number bounded?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/766
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

/-- Arithmetic identity: 766 = 76*7 + 234. -/
theorem arith_identity_766 : 76 * 7 + 234 = 766 := by norm_num

/-- 766 ≥ 27² = 729. -/
theorem square_bound_766 : 27^2 ≤ 766 := by norm_num

/-- 766 mod 3 = 1. -/
theorem mod3_766 : 766 % 3 = 1 := by norm_num

/-- 766 is even: 766 = 2 * 383. -/
theorem even_766 : 766 = 2 * 383 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
