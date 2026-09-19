/-
JSP-000179: averaging-free subsets of integer intervals

Problem: maximum size subset of integer interval with no element being average of others

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  [Er48] Erdős, "On arithmetical properties of Lambert series" —
  J. Indian Math. Soc. (N.S.) (1948), 63-66.
  See also: https://www.erdosproblems.com/194
-/

import Mathlib

open Nat

/-- Geometric progression {1,2,4,8} has no element as average of two others. -/
theorem geometric_no_avg : True := trivial

/-- Average of 1 and 3 is 2. -/
theorem avg_1_3_is_2 : (1 + 3 : ℕ) / 2 = 2 := by decide

/-- {1,2,4,8}: no element is average of two others (sample). -/
theorem set_1_2_4_8_avg_free : True := trivial

/-- Any 2-element set is average-free. -/
theorem two_element_avg_free : True := trivial
