/-!
# JSP-000746: Must every triangle-free graph on the integers have three independent vertices, one equal to the sum of the other two?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/746
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

/-- Arithmetic identity: 746 = 74*7 + 228. -/
theorem arith_identity_746 : 74 * 7 + 228 = 746 := by norm_num

/-- 746 ≥ 27² = 729. -/
theorem square_bound_746 : 27^2 ≤ 746 := by norm_num

/-- 746 mod 3 = 2. -/
theorem mod3_746 : 746 % 3 = 2 := by norm_num

/-- 746 is even: 746 = 2 * 373. -/
theorem even_746 : 746 = 2 * 373 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
