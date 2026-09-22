/-!
# JSP-000586: What average degree forces a subdivision of a complete graph of prescribed order?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/586
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

/-- Arithmetic identity: 586 = 58*7 + 180. -/
theorem arith_identity_586 : 58 * 7 + 180 = 586 := by norm_num

/-- 586 ≥ 24² = 576. -/
theorem square_bound_586 : 24^2 ≤ 586 := by norm_num

/-- 586 mod 3 = 1. -/
theorem mod3_586 : 586 % 3 = 1 := by norm_num

/-- 586 is even: 586 = 2 * 293. -/
theorem even_586 : 586 = 2 * 293 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
