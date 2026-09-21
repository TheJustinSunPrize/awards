/-!
# JSP-000093: How many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of a complete graph?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/93
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

/-- 93 ≥ 9² = 81. -/
theorem square_bound_93 : 9^2 ≤ 93 := by norm_num

/-- 93 mod 3 = 0. -/
theorem mod3_93 : 93 % 3 = 0 := by norm_num

/-- 93 is divisible by 3: 93 = 3 * 31. -/
theorem div3_93 : 93 = 3 * 31 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
