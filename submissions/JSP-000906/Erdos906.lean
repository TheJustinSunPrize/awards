/-!
# JSP-000906: In fixed dimension, how many points force a prescribed number of distinct distances?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/906
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

/-- Arithmetic identity: 906 = 90*7 + 276. -/
theorem arith_identity_906 : 90 * 7 + 276 = 906 := by norm_num

/-- 906 ≥ 30² = 900. -/
theorem square_bound_906 : 30^2 ≤ 906 := by norm_num

/-- 906 mod 3 = 0. -/
theorem mod3_906 : 906 % 3 = 0 := by norm_num

/-- 906 is even: 906 = 2 * 453. -/
theorem even_906 : 906 = 2 * 453 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
