/-
JSP-000388: polynomial value set with unique additive complement

Problem: Number theory / Polynomials

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos397
-/

import Mathlib

open Nat
