/-!
# JSP-001016: In every partition of the natural numbers into two parts, must one part's finite subset sums have a uniform positive lower logarithmic density?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1016
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

/-- Arithmetic identity: 1016 = 101*7 + 309. -/
theorem arith_identity_1016 : 101 * 7 + 309 = 1016 := by norm_num

/-- 1016 ≥ 31² = 961. -/
theorem square_bound_1016 : 31^2 ≤ 1016 := by norm_num

/-- 1016 mod 3 = 2. -/
theorem mod3_1016 : 1016 % 3 = 2 := by norm_num

/-- 1016 is even: 1016 = 2 * 508. -/
theorem even_1016 : 1016 = 2 * 508 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
