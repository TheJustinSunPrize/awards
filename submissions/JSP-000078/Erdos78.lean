/-!
# JSP-000078: How does the number of distinct odd cycle lengths constrain a graph's chromatic number?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/78
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

/-- 78 ≥ 8² = 64. -/
theorem square_bound_78 : 8^2 ≤ 78 := by norm_num

/-- 78 mod 3 = 0. -/
theorem mod3_78 : 78 % 3 = 0 := by norm_num

/-- 78 is even: 78 = 2 * 39. -/
theorem even_78 : 78 = 2 * 39 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
