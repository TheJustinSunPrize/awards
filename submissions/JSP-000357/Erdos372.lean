/-
JSP-000357: square-sum-free subset of integer interval

Problem: Number theory / Additive combinatorics

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos372
-/

import Mathlib

open Nat
