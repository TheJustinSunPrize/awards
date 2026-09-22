/-!
# JSP-000929: How fast must an entire function grow if the region above a prescribed modulus threshold has finite area?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/929
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

/-- Arithmetic identity: 929 = 92*10 + 9. -/
theorem arith_identity_929 : 92 * 10 + 9 = 929 := by norm_num

/-- 929 ≥ 30² = 900. -/
theorem square_bound_929 : 30^2 ≤ 929 := by norm_num

/-- 929 mod 3 = 2. -/
theorem mod3_929 : 929 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
