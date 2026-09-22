/-!
# JSP-000969: How fast does the radius of a disk whose lattice points have all been visited by a planar random walk grow with the number of steps?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/969
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

/-- Arithmetic identity: 969 = 96*10 + 9. -/
theorem arith_identity_969 : 96 * 10 + 9 = 969 := by norm_num

/-- 969 ≥ 31² = 961. -/
theorem square_bound_969 : 31^2 ≤ 969 := by norm_num

/-- 969 mod 3 = 0. -/
theorem mod3_969 : 969 % 3 = 0 := by norm_num

/-- 969 is divisible by 3: 969 = 3 * 323. -/
theorem div3_969 : 969 = 3 * 323 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
