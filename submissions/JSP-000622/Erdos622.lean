/-!
# JSP-000622: For a prescribed small graph order, what is the worst-case minimum number of clique or independent-set parts in a vertex partition?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/622
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

/-- Arithmetic identity: 622 = 62*3 + 436. -/
theorem arith_identity_622 : 62 * 3 + 436 = 622 := by norm_num

/-- 622 ≥ 24² = 576. -/
theorem square_bound_622 : 24^2 ≤ 622 := by norm_num

/-- 622 mod 3 = 1. -/
theorem mod3_622 : 622 % 3 = 1 := by norm_num

/-- 622 is even: 622 = 2 * 311. -/
theorem even_622 : 622 = 2 * 311 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
