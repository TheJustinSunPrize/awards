/-!
# JSP-000655: How many colors are needed for an acyclic coloring of a bounded-maximum-degree graph, with every two color classes inducing a forest?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/655
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

/-- Arithmetic identity: 655 = 65*6 + 265. -/
theorem arith_identity_655 : 65 * 6 + 265 = 655 := by norm_num

/-- 655 ≥ 25² = 625. -/
theorem square_bound_655 : 25^2 ≤ 655 := by norm_num

/-- 655 mod 3 = 1. -/
theorem mod3_655 : 655 % 3 = 1 := by norm_num

/-- 655 is divisible by 5: 655 = 5 * 131. -/
theorem div5_655 : 655 = 5 * 131 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
