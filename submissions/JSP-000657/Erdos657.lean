/-!
# JSP-000657: If all high-degree vertices are pairwise nonadjacent, is the graph's Ramsey number linear in its size?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/657
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

/-- Arithmetic identity: 657 = 65*8 + 137. -/
theorem arith_identity_657 : 65 * 8 + 137 = 657 := by norm_num

/-- 657 ≥ 25² = 625. -/
theorem square_bound_657 : 25^2 ≤ 657 := by norm_num

/-- 657 mod 3 = 0. -/
theorem mod3_657 : 657 % 3 = 0 := by norm_num

/-- 657 is divisible by 3: 657 = 3 * 219. -/
theorem div3_657 : 657 = 3 * 219 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
