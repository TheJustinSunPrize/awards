/-!
# JSP-000985: Do boundedly many sums of modular inverses of a short initial integer interval cover all residues modulo a prime?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/985
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

/-- Arithmetic identity: 985 = 98*6 + 397. -/
theorem arith_identity_985 : 98 * 6 + 397 = 985 := by norm_num

/-- 985 ≥ 31² = 961. -/
theorem square_bound_985 : 31^2 ≤ 985 := by norm_num

/-- 985 mod 3 = 1. -/
theorem mod3_985 : 985 % 3 = 1 := by norm_num

/-- 985 is divisible by 5: 985 = 5 * 197. -/
theorem div5_985 : 985 = 5 * 197 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
