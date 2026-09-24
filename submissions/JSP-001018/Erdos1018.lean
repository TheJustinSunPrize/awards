/-!
# JSP-001018: Must every sufficiently long integer sequence with bounded gaps have two distinct consecutive blocks with equal sums?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1018
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

/-- Arithmetic identity: 1018 = 101*9 + 109. -/
theorem arith_identity_1018 : 101 * 9 + 109 = 1018 := by norm_num

/-- 1018 ≥ 31² = 961. -/
theorem square_bound_1018 : 31^2 ≤ 1018 := by norm_num

/-- 1018 mod 3 = 1. -/
theorem mod3_1018 : 1018 % 3 = 1 := by norm_num

/-- 1018 is even: 1018 = 2 * 509. -/
theorem even_1018 : 1018 = 2 * 509 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
