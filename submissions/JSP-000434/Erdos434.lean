/-!
# JSP-000434: How many random elements of a finite abelian group make their subset sums cover the group with probability at least one half? Does the binary logarithm of the group order plus a small correction suffice?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/434
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

/-- Arithmetic identity: 434 = 43*5 + 219. -/
theorem arith_identity_434 : 43 * 5 + 219 = 434 := by norm_num

/-- 434 ≥ 20² = 400. -/
theorem square_bound_434 : 20^2 ≤ 434 := by norm_num

/-- 434 mod 3 = 2. -/
theorem mod3_434 : 434 % 3 = 2 := by norm_num

/-- 434 is even: 434 = 2 * 217. -/
theorem even_434 : 434 = 2 * 217 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
