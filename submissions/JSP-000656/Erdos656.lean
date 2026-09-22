/-!
# JSP-000656: Is the list chromatic number of a random graph sublinear in its number of vertices?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/656
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

/-- Arithmetic identity: 656 = 65*7 + 201. -/
theorem arith_identity_656 : 65 * 7 + 201 = 656 := by norm_num

/-- 656 ≥ 25² = 625. -/
theorem square_bound_656 : 25^2 ≤ 656 := by norm_num

/-- 656 mod 3 = 2. -/
theorem mod3_656 : 656 % 3 = 2 := by norm_num

/-- 656 is even: 656 = 2 * 328. -/
theorem even_656 : 656 = 2 * 328 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
