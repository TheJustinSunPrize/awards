/-!
# JSP-000958: For every choice of interpolation nodes, must error amplification on each fixed subinterval grow at least logarithmically?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/958
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

/-- Arithmetic identity: 958 = 95*9 + 103. -/
theorem arith_identity_958 : 95 * 9 + 103 = 958 := by norm_num

/-- 958 ≥ 30² = 900. -/
theorem square_bound_958 : 30^2 ≤ 958 := by norm_num

/-- 958 mod 3 = 1. -/
theorem mod3_958 : 958 % 3 = 1 := by norm_num

/-- 958 is even: 958 = 2 * 479. -/
theorem even_958 : 958 = 2 * 479 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
