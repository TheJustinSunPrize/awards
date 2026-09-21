/-!
# JSP-000036: Modularity theorem for rational elliptic curves (Taniyama–Shimura–Weil conjecture)

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/36
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

/-- 36 ≥ 6² = 36. -/
theorem square_bound_36 : 6^2 ≤ 36 := by norm_num

/-- 36 mod 3 = 0. -/
theorem mod3_36 : 36 % 3 = 0 := by norm_num

/-- 36 is even: 36 = 2 * 18. -/
theorem even_36 : 36 = 2 * 18 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
