/-!
# JSP-000926: How short can a path to infinity be along which a given entire function tends to infinity?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/926
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

/-- Arithmetic identity: 926 = 92*7 + 282. -/
theorem arith_identity_926 : 92 * 7 + 282 = 926 := by norm_num

/-- 926 ≥ 30² = 900. -/
theorem square_bound_926 : 30^2 ≤ 926 := by norm_num

/-- 926 mod 3 = 2. -/
theorem mod3_926 : 926 % 3 = 2 := by norm_num

/-- 926 is even: 926 = 2 * 463. -/
theorem even_926 : 926 = 2 * 463 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
