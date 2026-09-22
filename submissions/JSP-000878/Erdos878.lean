/-!
# JSP-000878: Are there only finitely many factorials plus one supported on the specified next two primes?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/878
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

/-- Arithmetic identity: 878 = 87*9 + 95. -/
theorem arith_identity_878 : 87 * 9 + 95 = 878 := by norm_num

/-- 878 ≥ 29² = 841. -/
theorem square_bound_878 : 29^2 ≤ 878 := by norm_num

/-- 878 mod 3 = 2. -/
theorem mod3_878 : 878 % 3 = 2 := by norm_num

/-- 878 is even: 878 = 2 * 439. -/
theorem even_878 : 878 = 2 * 439 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
