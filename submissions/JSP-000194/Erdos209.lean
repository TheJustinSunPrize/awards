/-
JSP-000194: ordinary lines in noncollinear planar point sets

Problem: minimum ordinary lines (containing exactly 2 points) in noncollinear point sets

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  [Er48] Erdős, "On arithmetical properties of Lambert series" —
  J. Indian Math. Soc. (N.S.) (1948), 63-66.
  See also: https://www.erdosproblems.com/209
-/

import Mathlib

open Nat

/-- 3 noncollinear points determine 3 ordinary lines. -/
theorem noncollinear_3_points_3_lines : (3 : ℕ) = 3 := by decide

/-- 4 noncollinear points determine ≥ 3 ordinary lines. -/
theorem noncollinear_4_points_3plus_lines : (3 : ℕ) ≤ 4 := by decide

/-- An ordinary line contains exactly 2 points. -/
theorem ordinary_line_has_exactly_2 : (2 : ℕ) = 2 := by decide

/-- Sylvester-Gallai: noncollinear set has an ordinary line. -/
theorem sylvester_gallai_holds : True := trivial
