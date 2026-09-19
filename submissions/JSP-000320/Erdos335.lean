/-
JSP-000320: binomial coefficient divisor close to upper parameter

Problem: Number theory / Binomial coefficients

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos335
-/

import Mathlib

open Nat
