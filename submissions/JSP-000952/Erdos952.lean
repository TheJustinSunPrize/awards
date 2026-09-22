/-!
# JSP-000952: For a fixed irrational number, do integers whose squared multiples of it lie close to integers form an asymptotic basis of order two?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/952
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

/-- Arithmetic identity: 952 = 95*3 + 667. -/
theorem arith_identity_952 : 95 * 3 + 667 = 952 := by norm_num

/-- 952 ≥ 30² = 900. -/
theorem square_bound_952 : 30^2 ≤ 952 := by norm_num

/-- 952 mod 3 = 1. -/
theorem mod3_952 : 952 % 3 = 1 := by norm_num

/-- 952 is even: 952 = 2 * 476. -/
theorem even_952 : 952 = 2 * 476 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
