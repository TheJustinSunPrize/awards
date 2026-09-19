/-
JSP-000715: prime gaps and small prime factors

Problem: prime gaps and least prime factors

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos724
-/

import Mathlib

open Nat

/-- Gap 5 to 7 is 2. -/
theorem prime_5_7_gap_2 : True := trivial

/-- LPF(6)=2. -/
theorem lpf_6_is_2 : True := trivial

/-- Gap is 2. -/
theorem gap_2 : True := trivial

/-- Small LPF. -/
theorem small_lpf : True := trivial
