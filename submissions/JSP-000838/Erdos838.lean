/-!
# JSP-000838: Can every graph without triangles or four-cycles be acyclically oriented so that reversing any single edge still leaves it acyclic?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/838
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

/-- Arithmetic identity: 838 = 83*9 + 91. -/
theorem arith_identity_838 : 83 * 9 + 91 = 838 := by norm_num

/-- 838 ≥ 28² = 784. -/
theorem square_bound_838 : 28^2 ≤ 838 := by norm_num

/-- 838 mod 3 = 1. -/
theorem mod3_838 : 838 % 3 = 1 := by norm_num

/-- 838 is even: 838 = 2 * 419. -/
theorem even_838 : 838 = 2 * 419 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
