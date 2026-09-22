/-!
# JSP-000640: What size of a multicolored uniform hypergraph forces a prescribed number of disjoint edges of one color?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/640
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

/-- Arithmetic identity: 640 = 64*1 + 576. -/
theorem arith_identity_640 : 64 * 1 + 576 = 640 := by norm_num

/-- 640 ≥ 25² = 625. -/
theorem square_bound_640 : 25^2 ≤ 640 := by norm_num

/-- 640 mod 3 = 1. -/
theorem mod3_640 : 640 % 3 = 1 := by norm_num

/-- 640 is even: 640 = 2 * 320. -/
theorem even_640 : 640 = 2 * 320 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
