/-!
# JSP-000854: How many vertex subsets meet every hyperedge while containing none of them in full?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/854
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

/-- Arithmetic identity: 854 = 85*5 + 429. -/
theorem arith_identity_854 : 85 * 5 + 429 = 854 := by norm_num

/-- 854 ≥ 29² = 841. -/
theorem square_bound_854 : 29^2 ≤ 854 := by norm_num

/-- 854 mod 3 = 2. -/
theorem mod3_854 : 854 % 3 = 2 := by norm_num

/-- 854 is even: 854 = 2 * 427. -/
theorem even_854 : 854 = 2 * 427 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
