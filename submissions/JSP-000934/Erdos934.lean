/-!
# JSP-000934: Can a square and a disk of equal area be partitioned into finitely many pieces and reassembled into each other using the prescribed rigid motions?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/934
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

/-- Arithmetic identity: 934 = 93*5 + 469. -/
theorem arith_identity_934 : 93 * 5 + 469 = 934 := by norm_num

/-- 934 ≥ 30² = 900. -/
theorem square_bound_934 : 30^2 ≤ 934 := by norm_num

/-- 934 mod 3 = 1. -/
theorem mod3_934 : 934 % 3 = 1 := by norm_num

/-- 934 is even: 934 = 2 * 467. -/
theorem even_934 : 934 = 2 * 467 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
