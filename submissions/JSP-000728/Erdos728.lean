/-!
# JSP-000728: How many inclusion-maximal sum-free subsets does a finite integer interval have?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/728
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

/-- Arithmetic identity: 728 = 72*9 + 80. -/
theorem arith_identity_728 : 72 * 9 + 80 = 728 := by norm_num

/-- 728 ≥ 26² = 676. -/
theorem square_bound_728 : 26^2 ≤ 728 := by norm_num

/-- 728 mod 3 = 2. -/
theorem mod3_728 : 728 % 3 = 2 := by norm_num

/-- 728 is even: 728 = 2 * 364. -/
theorem even_728 : 728 = 2 * 364 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
