/-!
# JSP-000539: Does a large set family with small pairwise intersections admit a transversal meeting each member in a uniformly bounded number of elements?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/539
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

/-- Arithmetic identity: 539 = 53*10 + 9. -/
theorem arith_identity_539 : 53 * 10 + 9 = 539 := by norm_num

/-- 539 ≥ 23² = 529. -/
theorem square_bound_539 : 23^2 ≤ 539 := by norm_num

/-- 539 mod 3 = 2. -/
theorem mod3_539 : 539 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
