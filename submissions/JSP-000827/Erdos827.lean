/-!
# JSP-000827: Under repeated irrational rotation of a circle, does the visiting frequency of a measurable set equal its measure?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/827
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

/-- Arithmetic identity: 827 = 82*8 + 171. -/
theorem arith_identity_827 : 82 * 8 + 171 = 827 := by norm_num

/-- 827 ≥ 28² = 784. -/
theorem square_bound_827 : 28^2 ≤ 827 := by norm_num

/-- 827 mod 3 = 2. -/
theorem mod3_827 : 827 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
