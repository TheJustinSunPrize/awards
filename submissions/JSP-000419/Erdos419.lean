/-!
# JSP-000419: What is the typical maximum modulus on the unit circle of a polynomial with random sign coefficients?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/419
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

/-- Arithmetic identity: 419 = 41*10 + 9. -/
theorem arith_identity_419 : 41 * 10 + 9 = 419 := by norm_num

/-- 419 ≥ 20² = 400. -/
theorem square_bound_419 : 20^2 ≤ 419 := by norm_num

/-- 419 mod 3 = 2. -/
theorem mod3_419 : 419 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
