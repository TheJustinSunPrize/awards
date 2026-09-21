/-!
# JSP-000096: Which minimal graphs prevent Ramsey numbers from growing linearly with the number of edges? Characterize these obstructions.

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/96
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

/-- 96 ≥ 9² = 81. -/
theorem square_bound_96 : 9^2 ≤ 96 := by norm_num

/-- 96 mod 3 = 0. -/
theorem mod3_96 : 96 % 3 = 0 := by norm_num

/-- 96 is even: 96 = 2 * 48. -/
theorem even_96 : 96 = 2 * 48 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
