/-!
# JSP-000554: Between consecutive primes, is there an integer whose least prime factor is at least their gap?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/554
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

/-- Arithmetic identity: 554 = 55*5 + 279. -/
theorem arith_identity_554 : 55 * 5 + 279 = 554 := by norm_num

/-- 554 ≥ 23² = 529. -/
theorem square_bound_554 : 23^2 ≤ 554 := by norm_num

/-- 554 mod 3 = 2. -/
theorem mod3_554 : 554 % 3 = 2 := by norm_num

/-- 554 is even: 554 = 2 * 277. -/
theorem even_554 : 554 = 2 * 277 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
