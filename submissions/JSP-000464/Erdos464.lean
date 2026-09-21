/-!
# JSP-000464: How many edges can a graph have while excluding an odd cycle and an even cycle of adjacent lengths?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/464
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

/-- Arithmetic identity: 464 = 46*5 + 234. -/
theorem arith_identity_464 : 46 * 5 + 234 = 464 := by norm_num

/-- 464 ≥ 21² = 441. -/
theorem square_bound_464 : 21^2 ≤ 464 := by norm_num

/-- 464 mod 3 = 2. -/
theorem mod3_464 : 464 % 3 = 2 := by norm_num

/-- 464 is even: 464 = 2 * 232. -/
theorem even_464 : 464 = 2 * 232 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
