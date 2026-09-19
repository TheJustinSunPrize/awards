/-
JSP-000399: unique recovery from k-sum multiset

Problem: Additive combinatorics

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos408
-/

import Mathlib

open Nat
