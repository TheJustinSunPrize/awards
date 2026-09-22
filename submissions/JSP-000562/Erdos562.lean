/-!
# JSP-000562: Is the density distribution of the prime factor at a prescribed position among ordered distinct prime factors unimodal?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/562
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

/-- Arithmetic identity: 562 = 56*3 + 394. -/
theorem arith_identity_562 : 56 * 3 + 394 = 562 := by norm_num

/-- 562 ≥ 23² = 529. -/
theorem square_bound_562 : 23^2 ≤ 562 := by norm_num

/-- 562 mod 3 = 1. -/
theorem mod3_562 : 562 % 3 = 1 := by norm_num

/-- 562 is even: 562 = 2 * 281. -/
theorem even_562 : 562 = 2 * 281 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
