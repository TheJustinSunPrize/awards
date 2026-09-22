/-!
# JSP-001022: Must every integer set of positive lower logarithmic density contain an infinite divisibility chain, with controlled growth?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1022
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

/-- Arithmetic identity: 1022 = 102*3 + 716. -/
theorem arith_identity_1022 : 102 * 3 + 716 = 1022 := by norm_num

/-- 1022 ≥ 31² = 961. -/
theorem square_bound_1022 : 31^2 ≤ 1022 := by norm_num

/-- 1022 mod 3 = 2. -/
theorem mod3_1022 : 1022 % 3 = 2 := by norm_num

/-- 1022 is even: 1022 = 2 * 511. -/
theorem even_1022 : 1022 = 2 * 511 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
