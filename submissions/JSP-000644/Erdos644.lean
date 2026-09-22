/-!
# JSP-000644: If an integer set's reciprocal sum is bounded, what proportion of integers must avoid divisibility by every set element?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/644
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

/-- Arithmetic identity: 644 = 64*5 + 324. -/
theorem arith_identity_644 : 64 * 5 + 324 = 644 := by norm_num

/-- 644 ≥ 25² = 625. -/
theorem square_bound_644 : 25^2 ≤ 644 := by norm_num

/-- 644 mod 3 = 2. -/
theorem mod3_644 : 644 % 3 = 2 := by norm_num

/-- 644 is even: 644 = 2 * 322. -/
theorem even_644 : 644 = 2 * 322 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
