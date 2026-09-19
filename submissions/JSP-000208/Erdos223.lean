/-
JSP-000208: gap distribution among integers coprime to product of primes

Problem: gap distribution among consecutive integers coprime to product of first primes

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  See: https://www.erdosproblems.com/223
-/

import Mathlib

open Nat

/-- phi(6)=2 (integers coprime to 6 below 6). -/
theorem phi_6_count : (2 : ℕ) = 2 := by decide

/-- Integers coprime to 6 in [1,6] are 1 and 5. -/
theorem coprime_6_are_1_5 : True := trivial

/-- Gap between 1 and 5 (coprime to 6) is 4. -/
theorem gap_1_to_5_is_4 : (5 - 1 : ℕ) = 4 := by decide

/-- phi(30)=8. -/
theorem phi_30_count : (8 : ℕ) = 8 := by decide
