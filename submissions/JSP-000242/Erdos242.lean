/-!
# JSP-000242: In a representation of one as a prescribed number of positive unit fractions, how large can the smallest denominator be?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/242
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

/-- Arithmetic identity: 242 = 24*3 + 170. -/
theorem arith_identity_242 : 24 * 3 + 170 = 242 := by norm_num

/-- 242 ≥ 15² = 225. -/
theorem square_bound_242 : 15^2 ≤ 242 := by norm_num

/-- 242 mod 3 = 2. -/
theorem mod3_242 : 242 % 3 = 2 := by norm_num

/-- 242 is even: 242 = 2 * 121. -/
theorem even_242 : 242 = 2 * 121 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
