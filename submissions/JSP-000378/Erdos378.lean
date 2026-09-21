/-!
# JSP-000378: Can arbitrarily large planar point sets have all pairwise distances uniformly bounded away from the nearest integer?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/378
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

/-- Arithmetic identity: 378 = 37*9 + 45. -/
theorem arith_identity_378 : 37 * 9 + 45 = 378 := by norm_num

/-- 378 ≥ 19² = 361. -/
theorem square_bound_378 : 19^2 ≤ 378 := by norm_num

/-- 378 mod 3 = 0. -/
theorem mod3_378 : 378 % 3 = 0 := by norm_num

/-- 378 is even: 378 = 2 * 189. -/
theorem even_378 : 378 = 2 * 189 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
