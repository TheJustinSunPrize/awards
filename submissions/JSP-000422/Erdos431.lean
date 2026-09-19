/-
JSP-000422: arc length conditions for random circle coverage

Problem: Probability / Geometry

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos431
-/

import Mathlib

open Nat
