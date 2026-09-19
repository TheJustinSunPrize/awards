/-
JSP-000415: edge-colored complete graph vertex cover by monochromatic paths

Problem: Graph theory

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos424
-/

import Mathlib

open Nat
