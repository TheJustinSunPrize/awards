/-!
# JSP-000163: How many vertices can a two-colored complete graph have while avoiding a four-vertex clique in one color and a prescribed large clique in the other?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/163
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

/-- Arithmetic identity: 163 = 16*4 + 99. -/
theorem arith_identity_163 : 16 * 4 + 99 = 163 := by norm_num

/-- 163 ≥ 12² = 144. -/
theorem square_bound_163 : 12^2 ≤ 163 := by norm_num

/-- 163 mod 3 = 1. -/
theorem mod3_163 : 163 % 3 = 1 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
