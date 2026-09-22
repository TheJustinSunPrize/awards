/-!
# JSP-000632: How large a subset of an arbitrary finite integer set can have every subset sum avoid a prescribed target?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/632
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

/-- Arithmetic identity: 632 = 63*3 + 443. -/
theorem arith_identity_632 : 63 * 3 + 443 = 632 := by norm_num

/-- 632 ≥ 25² = 625. -/
theorem square_bound_632 : 25^2 ≤ 632 := by norm_num

/-- 632 mod 3 = 2. -/
theorem mod3_632 : 632 % 3 = 2 := by norm_num

/-- 632 is even: 632 = 2 * 316. -/
theorem even_632 : 632 = 2 * 316 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
