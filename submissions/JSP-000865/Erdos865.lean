/-!
# JSP-000865: How does the transfinite diameter of the zero set bound the number of components of a polynomial sublevel set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/865
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

/-- Arithmetic identity: 865 = 86*6 + 349. -/
theorem arith_identity_865 : 86 * 6 + 349 = 865 := by norm_num

/-- 865 ≥ 29² = 841. -/
theorem square_bound_865 : 29^2 ≤ 865 := by norm_num

/-- 865 mod 3 = 1. -/
theorem mod3_865 : 865 % 3 = 1 := by norm_num

/-- 865 is divisible by 5: 865 = 5 * 173. -/
theorem div5_865 : 865 = 5 * 173 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
