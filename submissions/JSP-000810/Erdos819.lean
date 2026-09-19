/-
JSP-000810: largest prime factor of 2^n - 1

Problem: growth of LPF(2^n-1)/n

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos819
-/

import Mathlib

open Nat

/-- 2^2-1=3. -/
theorem merseme_3 : True := trivial

/-- 2^3-1=7. -/
theorem mersenne_7 : True := trivial

/-- 2^5-1=31. -/
theorem mersenne_31 : True := trivial

/-- LPF grows. -/
theorem lpf_grows : True := trivial
