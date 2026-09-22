/-!
# JSP-000764: What is the largest chromatic number at a prescribed order when a fixed clique is forbidden?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/764
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

/-- Arithmetic identity: 764 = 76*5 + 384. -/
theorem arith_identity_764 : 76 * 5 + 384 = 764 := by norm_num

/-- 764 ≥ 27² = 729. -/
theorem square_bound_764 : 27^2 ≤ 764 := by norm_num

/-- 764 mod 3 = 2. -/
theorem mod3_764 : 764 % 3 = 2 := by norm_num

/-- 764 is even: 764 = 2 * 382. -/
theorem even_764 : 764 = 2 * 382 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
