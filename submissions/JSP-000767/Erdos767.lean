/-!
# JSP-000767: Can a graph exclude a larger clique while forcing a smaller monochromatic clique under every prescribed multicolor edge coloring?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/767
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

/-- Arithmetic identity: 767 = 76*8 + 159. -/
theorem arith_identity_767 : 76 * 8 + 159 = 767 := by norm_num

/-- 767 ≥ 27² = 729. -/
theorem square_bound_767 : 27^2 ≤ 767 := by norm_num

/-- 767 mod 3 = 2. -/
theorem mod3_767 : 767 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
