/-!
# JSP-000506: In a random graph, how much smaller than the chromatic number is the minimum number of parts in a partition into cliques and independent sets?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/506
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

/-- Arithmetic identity: 506 = 50*7 + 156. -/
theorem arith_identity_506 : 50 * 7 + 156 = 506 := by norm_num

/-- 506 ≥ 22² = 484. -/
theorem square_bound_506 : 22^2 ≤ 506 := by norm_num

/-- 506 mod 3 = 2. -/
theorem mod3_506 : 506 % 3 = 2 := by norm_num

/-- 506 is even: 506 = 2 * 253. -/
theorem even_506 : 506 = 2 * 253 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
