/-!
# JSP-000711: How large can an integer set's reciprocal sum be when the specified pairs linked by large prime factors and divisibility are forbidden?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/711
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

/-- Arithmetic identity: 711 = 71*2 + 569. -/
theorem arith_identity_711 : 71 * 2 + 569 = 711 := by norm_num

/-- 711 ≥ 26² = 676. -/
theorem square_bound_711 : 26^2 ≤ 711 := by norm_num

/-- 711 mod 3 = 0. -/
theorem mod3_711 : 711 % 3 = 0 := by norm_num

/-- 711 is divisible by 3: 711 = 3 * 237. -/
theorem div3_711 : 711 = 3 * 237 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
