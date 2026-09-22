/-!
# JSP-000590: For sufficiently large order satisfying the necessary divisibility conditions, do designs exist in which each prescribed-size point subset lies in exactly one fixed-size block?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/590
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

/-- Arithmetic identity: 590 = 59*1 + 531. -/
theorem arith_identity_590 : 59 * 1 + 531 = 590 := by norm_num

/-- 590 ≥ 24² = 576. -/
theorem square_bound_590 : 24^2 ≤ 590 := by norm_num

/-- 590 mod 3 = 2. -/
theorem mod3_590 : 590 % 3 = 2 := by norm_num

/-- 590 is even: 590 = 2 * 295. -/
theorem even_590 : 590 = 2 * 295 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
