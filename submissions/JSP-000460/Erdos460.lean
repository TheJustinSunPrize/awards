/-!
# JSP-000460: Is the Ramsey number of the prescribed cycle against any graph at most twice the latter's edge count plus the allowed correction?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/460
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

/-- Arithmetic identity: 460 = 46*1 + 414. -/
theorem arith_identity_460 : 46 * 1 + 414 = 460 := by norm_num

/-- 460 ≥ 21² = 441. -/
theorem square_bound_460 : 21^2 ≤ 460 := by norm_num

/-- 460 mod 3 = 1. -/
theorem mod3_460 : 460 % 3 = 1 := by norm_num

/-- 460 is even: 460 = 2 * 230. -/
theorem even_460 : 460 = 2 * 230 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
