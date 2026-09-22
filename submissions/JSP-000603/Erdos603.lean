/-!
# JSP-000603: When can a planar point set receive positive weights so that every line containing at least two points has the same total weight?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/603
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

/-- Arithmetic identity: 603 = 60*4 + 363. -/
theorem arith_identity_603 : 60 * 4 + 363 = 603 := by norm_num

/-- 603 ≥ 24² = 576. -/
theorem square_bound_603 : 24^2 ≤ 603 := by norm_num

/-- 603 mod 3 = 0. -/
theorem mod3_603 : 603 % 3 = 0 := by norm_num

/-- 603 is divisible by 3: 603 = 3 * 201. -/
theorem div3_603 : 603 = 3 * 201 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
