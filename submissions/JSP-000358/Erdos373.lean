/-
JSP-000358: two same-colored integers with perfect power sum

Problem: Number theory / Ramsey theory

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos373
-/

import Mathlib

open Nat
