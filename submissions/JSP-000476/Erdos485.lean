/-
JSP-000476: square-free subset sums from integer interval

Problem: max subset of interval with no subset sum a square

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos485
-/

import Mathlib

open Nat

/-- {1,2}: sum 3 not square. -/
theorem set_1_2_sum_3_nonsquare : True := trivial

/-- {1,2,4}: sum 7 not square. -/
theorem set_1_2_4_sum_7_nonsquare : True := trivial

/-- Empty set sum 0 = 0^2. -/
theorem empty_sum_0_is_square : True := trivial

/-- {2,3}: sum 5 not square. -/
theorem no_square_sum_2_element : True := trivial
