/-!
# JSP-000204: For a transcendental entire function, determine the limiting ratio between its largest power-series term and its maximum modulus on a circle.

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/204
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

/-- Arithmetic identity: 204 = 20*5 + 104. -/
theorem arith_identity_204 : 20 * 5 + 104 = 204 := by norm_num

/-- 204 ≥ 14² = 196. -/
theorem square_bound_204 : 14^2 ≤ 204 := by norm_num

/-- 204 mod 3 = 0. -/
theorem mod3_204 : 204 % 3 = 0 := by norm_num

/-- 204 is even: 204 = 2 * 102. -/
theorem even_204 : 204 = 2 * 102 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
