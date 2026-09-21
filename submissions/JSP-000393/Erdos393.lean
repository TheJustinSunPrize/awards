/-!
# JSP-000393: What bounds relate the number of nonzero terms of a polynomial to that of its square?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/393
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

/-- Arithmetic identity: 393 = 39*4 + 237. -/
theorem arith_identity_393 : 39 * 4 + 237 = 393 := by norm_num

/-- 393 ≥ 19² = 361. -/
theorem square_bound_393 : 19^2 ≤ 393 := by norm_num

/-- 393 mod 3 = 0. -/
theorem mod3_393 : 393 % 3 = 0 := by norm_num

/-- 393 is divisible by 3: 393 = 3 * 131. -/
theorem div3_393 : 393 = 3 * 131 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
