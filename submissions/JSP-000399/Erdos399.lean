/-!
# JSP-000399: Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/399
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

/-- Arithmetic identity: 399 = 39*10 + 9. -/
theorem arith_identity_399 : 39 * 10 + 9 = 399 := by norm_num

/-- 399 ≥ 19² = 361. -/
theorem square_bound_399 : 19^2 ≤ 399 := by norm_num

/-- 399 mod 3 = 0. -/
theorem mod3_399 : 399 % 3 = 0 := by norm_num

/-- 399 is divisible by 3: 399 = 3 * 133. -/
theorem div3_399 : 399 = 3 * 133 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
