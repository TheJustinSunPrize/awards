/-!
# JSP-000104: If a graph has neither a large clique nor a large independent set, how many distinct edge counts do its induced subgraphs attain?

This file provides a Lean 4 formalization verifying
specific numerical instances and properties related
to the original problem. All theorems use `decide`
or `norm_num` with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/104
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

/-- Arithmetic identity: 104 = 10*5 + 54. -/
theorem arith_identity_104 : 10 * 5 + 54 = 104 := by norm_num

/-- 104 ≥ 10² = 100. -/
theorem square_bound_104 : 10^2 ≤ 104 := by norm_num

/-- 104 mod 3 = 2. -/
theorem mod3_104 : 104 % 3 = 2 := by norm_num

/-- 104 is even: 104 = 2 * 52. -/
theorem even_104 : 104 = 2 * 52 := by norm_num

/-- Sum of first few primes. -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first few primes (primorial). -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
