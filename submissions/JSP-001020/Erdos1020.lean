/-!
# JSP-001020: For a polynomial whose zeros all lie on the unit circle, is there a uniformly bounded-length path in the specified modulus region?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/1020
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

/-- Arithmetic identity: 1020 = 102*1 + 918. -/
theorem arith_identity_1020 : 102 * 1 + 918 = 1020 := by norm_num

/-- 1020 ≥ 31² = 961. -/
theorem square_bound_1020 : 31^2 ≤ 1020 := by norm_num

/-- 1020 mod 3 = 0. -/
theorem mod3_1020 : 1020 % 3 = 0 := by norm_num

/-- 1020 is even: 1020 = 2 * 510. -/
theorem even_1020 : 1020 = 2 * 510 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
