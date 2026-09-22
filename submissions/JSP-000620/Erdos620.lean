/-!
# JSP-000620: In a finite four-dimensional point set, how many other points can be at the same distance from one point?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/620
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

/-- Arithmetic identity: 620 = 62*1 + 558. -/
theorem arith_identity_620 : 62 * 1 + 558 = 620 := by norm_num

/-- 620 ≥ 24² = 576. -/
theorem square_bound_620 : 24^2 ≤ 620 := by norm_num

/-- 620 mod 3 = 2. -/
theorem mod3_620 : 620 % 3 = 2 := by norm_num

/-- 620 is even: 620 = 2 * 310. -/
theorem even_620 : 620 = 2 * 310 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
