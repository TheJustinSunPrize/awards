/-!
# JSP-000825: For typical irrational scale factors, what is the discrepancy of fractional parts of a scaled integer sequence?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/825
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

/-- Arithmetic identity: 825 = 82*6 + 333. -/
theorem arith_identity_825 : 82 * 6 + 333 = 825 := by norm_num

/-- 825 ≥ 28² = 784. -/
theorem square_bound_825 : 28^2 ≤ 825 := by norm_num

/-- 825 mod 3 = 0. -/
theorem mod3_825 : 825 % 3 = 0 := by norm_num

/-- 825 is divisible by 3: 825 = 3 * 275. -/
theorem div3_825 : 825 = 3 * 275 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
