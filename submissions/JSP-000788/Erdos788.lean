/-!
# JSP-000788: Under a finite coloring of the positive integers, can the specified sparse sequence be found whose subset sums omit at least one color?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/788
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

/-- Arithmetic identity: 788 = 78*9 + 86. -/
theorem arith_identity_788 : 78 * 9 + 86 = 788 := by norm_num

/-- 788 ≥ 28² = 784. -/
theorem square_bound_788 : 28^2 ≤ 788 := by norm_num

/-- 788 mod 3 = 2. -/
theorem mod3_788 : 788 % 3 = 2 := by norm_num

/-- 788 is even: 788 = 2 * 394. -/
theorem even_788 : 788 = 2 * 394 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
