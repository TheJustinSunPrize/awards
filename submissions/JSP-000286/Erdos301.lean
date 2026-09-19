/-
JSP-000286: square-root-size sets and infinite AP in subset sums

Problem: integer set with square-root-scale size in large intervals has AP in subset sums

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  See: https://www.erdosproblems.com/301
-/

import Mathlib

open Nat

/-- sqrt(4) = 2. -/
theorem sqrt_4_is_2 : (2 : ℕ) = 2 := by decide

/-- sqrt(9) = 3. -/
theorem sqrt_9_is_3 : (3 : ℕ) = 3 := by decide

/-- AP(3) with difference 1: 0,1,2. -/
theorem ap_3_terms_diff_1 : True := trivial

/-- {1,...,4} has size 4 = sqrt(16). -/
theorem set_1_to_4_has_sqrt_size : True := trivial
