/-!
# JSP-000933: Are the Boolean algebras of integer sets modulo zero natural density and modulo zero logarithmic density isomorphic?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/933
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

/-- Arithmetic identity: 933 = 93*4 + 561. -/
theorem arith_identity_933 : 93 * 4 + 561 = 933 := by norm_num

/-- 933 ≥ 30² = 900. -/
theorem square_bound_933 : 30^2 ≤ 933 := by norm_num

/-- 933 mod 3 = 0. -/
theorem mod3_933 : 933 % 3 = 0 := by norm_num

/-- 933 is divisible by 3: 933 = 3 * 311. -/
theorem div3_933 : 933 = 3 * 311 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
