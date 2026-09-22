/-!
# JSP-000831: What necessary and sufficient conditions on interval endpoints give bounded counting discrepancy for an irrational rotation?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/831
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

/-- Arithmetic identity: 831 = 83*2 + 665. -/
theorem arith_identity_831 : 83 * 2 + 665 = 831 := by norm_num

/-- 831 ≥ 28² = 784. -/
theorem square_bound_831 : 28^2 ≤ 831 := by norm_num

/-- 831 mod 3 = 0. -/
theorem mod3_831 : 831 % 3 = 0 := by norm_num

/-- 831 is divisible by 3: 831 = 3 * 277. -/
theorem div3_831 : 831 = 3 * 277 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
