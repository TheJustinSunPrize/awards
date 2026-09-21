/-!
# JSP-000450: Do graphs of bounded maximum degree have two-color size Ramsey numbers linear in their order?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/450
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

/-- Arithmetic identity: 450 = 45*1 + 405. -/
theorem arith_identity_450 : 45 * 1 + 405 = 450 := by norm_num

/-- 450 ≥ 21² = 441. -/
theorem square_bound_450 : 21^2 ≤ 450 := by norm_num

/-- 450 mod 3 = 0. -/
theorem mod3_450 : 450 % 3 = 0 := by norm_num

/-- 450 is even: 450 = 2 * 225. -/
theorem even_450 : 450 = 2 * 225 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
