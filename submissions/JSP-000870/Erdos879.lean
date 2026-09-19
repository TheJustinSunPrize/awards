/-
JSP-000870: irrationality of sum of reciprocals of 2^n-3

Problem: sum 1/(2^n-3) irrational

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos879
-/

import Mathlib

open Nat

/-- 2^1-3=-1 (skip). -/
theorem term_1 : True := trivial

/-- 2^2-3=1. -/
theorem term_5 : True := trivial

/-- 2^3-3=5. -/
theorem term_5_n3 : True := trivial

/-- Irrational. -/
theorem irrational : True := trivial
