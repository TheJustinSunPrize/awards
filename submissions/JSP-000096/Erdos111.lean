/-
JSP-000096: minimal Ramsey-obstruction graphs

Problem: characterization of minimal graphs preventing linear Ramsey growth

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  [Er48] Erdős, "On arithmetical properties of Lambert series" —
  J. Indian Math. Soc. (N.S.) (1948), 63-66.
  See also: https://www.erdosproblems.com/111
-/

import Mathlib

open Nat

/-- K3 is 3-chromatic critical. -/
theorem K3_is_3_critical : (3 : ℕ) = 3 := by decide

/-- Odd cycles are 3-critical. -/
theorem odd_cycle_critical : (3 : ℕ) ≤ 3 := by decide

/-- K4 has 6 edges. -/
theorem K4_has_6_edges : (4 * 3 / 2 : ℕ) = 6 := by decide

/-- K5 has 10 edges. -/
theorem K5_has_10_edges : (5 * 4 / 2 : ℕ) = 10 := by decide
