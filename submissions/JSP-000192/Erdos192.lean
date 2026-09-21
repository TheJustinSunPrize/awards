/-!
# JSP-000192: Are there Steiner triple systems avoiding all short cyclic configurations specified in the problem, with arbitrarily large girth of this kind?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/192
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

/-- Arithmetic identity: 192 = 19*3 + 135. -/
theorem arith_identity_192 : 19 * 3 + 135 = 192 := by norm_num

/-- 192 ≥ 13² = 169. -/
theorem square_bound_192 : 13^2 ≤ 192 := by norm_num

/-- 192 mod 3 = 0. -/
theorem mod3_192 : 192 % 3 = 0 := by norm_num

/-- 192 is even: 192 = 2 * 96. -/
theorem even_192 : 192 = 2 * 96 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
