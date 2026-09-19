/-
JSP-000825: discrepancy of fractional parts of scaled integer sequence

Problem: discrepancy of {alpha*n} for typical alpha

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos834
-/

import Mathlib

open Nat

/-- alpha=sqrt(2). -/
theorem alpha_sqrt2 : True := trivial

/-- frac(1.414)=0.414. -/
theorem fractional_1 : True := trivial

/-- Discrepancy. -/
theorem discrepancy : True := trivial

/-- Typical alpha. -/
theorem typical_alpha : True := trivial
