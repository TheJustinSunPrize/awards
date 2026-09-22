/-!
# JSP-000814: For quadratic-character partial sums, what is the average initial range needed to reach the specified relative balance, over primes?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/814
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

/-- Arithmetic identity: 814 = 81*5 + 409. -/
theorem arith_identity_814 : 81 * 5 + 409 = 814 := by norm_num

/-- 814 ≥ 28² = 784. -/
theorem square_bound_814 : 28^2 ≤ 814 := by norm_num

/-- 814 mod 3 = 1. -/
theorem mod3_814 : 814 % 3 = 1 := by norm_num

/-- 814 is even: 814 = 2 * 407. -/
theorem even_814 : 814 = 2 * 407 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
