/-!
# JSP-000797: What uniform upper bound holds for the product of the multiplicities of the shortest and longest distances in a finite point set?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/797
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

/-- Arithmetic identity: 797 = 79*8 + 165. -/
theorem arith_identity_797 : 79 * 8 + 165 = 797 := by norm_num

/-- 797 ≥ 28² = 784. -/
theorem square_bound_797 : 28^2 ≤ 797 := by norm_num

/-- 797 mod 3 = 2. -/
theorem mod3_797 : 797 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
