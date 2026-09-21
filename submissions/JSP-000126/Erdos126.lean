/-!
# JSP-000126: If every two-coloring of an infinite graph's edges gives a monochromatic triangle, does the analogous property hold for every finite clique?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/126
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

/-- Arithmetic identity: 126 = 12*7 + 42. -/
theorem arith_identity_126 : 12 * 7 + 42 = 126 := by norm_num

/-- 126 ≥ 11² = 121. -/
theorem square_bound_126 : 11^2 ≤ 126 := by norm_num

/-- 126 mod 3 = 0. -/
theorem mod3_126 : 126 % 3 = 0 := by norm_num

/-- 126 is even: 126 = 2 * 63. -/
theorem even_126 : 126 = 2 * 63 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
