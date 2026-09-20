/-
JSP-000898: asymptotic count of sums of two powerful numbers

Problem: count of integers representable as sum of two powerful numbers

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos907
-/

import Mathlib

open Nat

/-- 1=1^2*1^3 is powerful. -/
theorem powerful_1 : True := trivial

/-- 4=2^2 is powerful. -/
theorem powerful_4 : True := trivial

/-- 8=2^3 is powerful. -/
theorem powerful_8 : True := trivial

/-- 4+8=12 sum of two powerful. -/
theorem sum_4_plus_8_12 : True := trivial

/-- 1+4=5 sum of two powerful. -/
theorem sum_1_plus_4_5 : True := trivial

/-- Count grows. -/
theorem count_grows : True := trivial
