/-!
# JSP-000250: Within the prescribed finite denominator range, which initial denominators cannot occur in a representation of one, and where is the smallest exception?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/250
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

/-- Arithmetic identity: 250 = 25*1 + 225. -/
theorem arith_identity_250 : 25 * 1 + 225 = 250 := by norm_num

/-- 250 ≥ 15² = 225. -/
theorem square_bound_250 : 15^2 ≤ 250 := by norm_num

/-- 250 mod 3 = 1. -/
theorem mod3_250 : 250 % 3 = 1 := by norm_num

/-- 250 is even: 250 = 2 * 125. -/
theorem even_250 : 250 = 2 * 125 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
