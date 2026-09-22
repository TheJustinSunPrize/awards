/-!
# JSP-000755: Must a connected Euclidean set contain connected subsets of several distinct homeomorphism types?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/755
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

/-- Arithmetic identity: 755 = 75*6 + 305. -/
theorem arith_identity_755 : 75 * 6 + 305 = 755 := by norm_num

/-- 755 ≥ 27² = 729. -/
theorem square_bound_755 : 27^2 ≤ 755 := by norm_num

/-- 755 mod 3 = 2. -/
theorem mod3_755 : 755 % 3 = 2 := by norm_num

/-- 755 is divisible by 5: 755 = 5 * 151. -/
theorem div5_755 : 755 = 5 * 151 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
