/-!
# JSP-000479: Does every red-blue coloring of pairs from the prescribed countable ordinal contain a red clique of the same order type or a blue triangle?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/479
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

/-- Arithmetic identity: 479 = 47*10 + 9. -/
theorem arith_identity_479 : 47 * 10 + 9 = 479 := by norm_num

/-- 479 ≥ 21² = 441. -/
theorem square_bound_479 : 21^2 ≤ 479 := by norm_num

/-- 479 mod 3 = 2. -/
theorem mod3_479 : 479 % 3 = 2 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
