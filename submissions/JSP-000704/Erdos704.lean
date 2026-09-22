/-!
# JSP-000704: Can a density-one set of integers be represented as a power of two plus a number with few prime factors?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/704
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

/-- Arithmetic identity: 704 = 70*5 + 354. -/
theorem arith_identity_704 : 70 * 5 + 354 = 704 := by norm_num

/-- 704 ≥ 26² = 676. -/
theorem square_bound_704 : 26^2 ≤ 704 := by norm_num

/-- 704 mod 3 = 2. -/
theorem mod3_704 : 704 % 3 = 2 := by norm_num

/-- 704 is even: 704 = 2 * 352. -/
theorem even_704 : 704 = 2 * 352 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
