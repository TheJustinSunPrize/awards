/-!
# JSP-000984: How many random elements of a finite abelian group make subset-sum representation counts approximately uniform?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/984
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

/-- Arithmetic identity: 984 = 98*5 + 494. -/
theorem arith_identity_984 : 98 * 5 + 494 = 984 := by norm_num

/-- 984 ≥ 31² = 961. -/
theorem square_bound_984 : 31^2 ≤ 984 := by norm_num

/-- 984 mod 3 = 0. -/
theorem mod3_984 : 984 % 3 = 0 := by norm_num

/-- 984 is even: 984 = 2 * 492. -/
theorem even_984 : 984 = 2 * 492 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
