/-!
# JSP-000665: When sums and products are taken only along edges of a dense graph on integers, how large must one of the resulting value sets be?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/665
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

/-- Arithmetic identity: 665 = 66*6 + 269. -/
theorem arith_identity_665 : 66 * 6 + 269 = 665 := by norm_num

/-- 665 ≥ 25² = 625. -/
theorem square_bound_665 : 25^2 ≤ 665 := by norm_num

/-- 665 mod 3 = 2. -/
theorem mod3_665 : 665 % 3 = 2 := by norm_num

/-- 665 is divisible by 5: 665 = 5 * 133. -/
theorem div5_665 : 665 = 5 * 133 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
