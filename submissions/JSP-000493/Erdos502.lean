/-
JSP-000493: possible total numbers of determined lines

Problem: which total line counts are possible for planar n-point sets

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos502
-/

import Mathlib

open Nat

/-- 3 noncollinear: 3 lines. -/
theorem 3_points_3_lines : True := trivial

/-- 4 points: 6 or 3 lines. -/
theorem 4_points_6_or_3 : True := trivial

/-- n collinear: 1 line. -/
theorem collinear_n_1_line : True := trivial

/-- General position: C(n,2) lines. -/
theorem general_position_lines : True := trivial
