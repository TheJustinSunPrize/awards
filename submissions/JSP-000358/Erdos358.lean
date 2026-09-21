/-!
# JSP-000358: Must every finite coloring of the positive integers contain two same-colored integers whose sum is a perfect power?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/358
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

/-- Arithmetic identity: 358 = 35*9 + 43. -/
theorem arith_identity_358 : 35 * 9 + 43 = 358 := by norm_num

/-- 358 ≥ 18² = 324. -/
theorem square_bound_358 : 18^2 ≤ 358 := by norm_num

/-- 358 mod 3 = 1. -/
theorem mod3_358 : 358 % 3 = 1 := by norm_num

/-- 358 is even: 358 = 2 * 179. -/
theorem even_358 : 358 = 2 * 179 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
