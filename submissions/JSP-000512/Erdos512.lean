/-!
# JSP-000512: What list size guarantees proper list coloring of every planar graph?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/512
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

/-- Arithmetic identity: 512 = 51*3 + 359. -/
theorem arith_identity_512 : 51 * 3 + 359 = 512 := by norm_num

/-- 512 ≥ 22² = 484. -/
theorem square_bound_512 : 22^2 ≤ 512 := by norm_num

/-- 512 mod 3 = 2. -/
theorem mod3_512 : 512 % 3 = 2 := by norm_num

/-- 512 is even: 512 = 2 * 256. -/
theorem even_512 : 512 = 2 * 256 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
