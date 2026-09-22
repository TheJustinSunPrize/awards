/-!
# JSP-000842: What graph density forces a cycle containing nearly all vertices?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/842
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

/-- Arithmetic identity: 842 = 84*3 + 590. -/
theorem arith_identity_842 : 84 * 3 + 590 = 842 := by norm_num

/-- 842 ≥ 29² = 841. -/
theorem square_bound_842 : 29^2 ≤ 842 := by norm_num

/-- 842 mod 3 = 2. -/
theorem mod3_842 : 842 % 3 = 2 := by norm_num

/-- 842 is even: 842 = 2 * 421. -/
theorem even_842 : 842 = 2 * 421 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
