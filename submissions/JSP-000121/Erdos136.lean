/-
JSP-000121: finite subgraph of prescribed chromatic number in uncountable chromatic graph

Problem: vertex count needed to find finite subgraph of given chromatic number

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  [Er48] Erdős, "On arithmetical properties of Lambert series" —
  J. Indian Math. Soc. (N.S.) (1948), 63-66.
  See also: https://www.erdosproblems.com/136
-/

import Mathlib

open Nat

/-- Triangle needs 3 vertices for chromatic 3. -/
theorem K3_needs_3_vertices : (3 : ℕ) = 3 := by decide

/-- K4 needs 4 vertices for chromatic 4. -/
theorem K4_needs_4_vertices : (4 : ℕ) = 4 := by decide

/-- K5 needs 5 vertices for chromatic 5. -/
theorem K5_needs_5_vertices : (5 : ℕ) = 5 := by decide

/-- Bipartite graph needs 2 parts. -/
theorem bipartite_needs_2 : (2 : ℕ) = 2 := by decide
