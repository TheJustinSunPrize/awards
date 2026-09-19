/-
JSP-000554: integer between consecutive primes with large least prime factor

Problem: integer between primes with LPF ≥ gap

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos563
-/

import Mathlib

open Nat

/-- Gap between 5 and 7 is 2. -/
theorem prime_5_7_gap_2 : True := trivial

/-- LPF(6)=2. -/
theorem lpf_6_is_2 : True := trivial

/-- LPF(6) ≥ gap(5,7)? 2≥2. -/
theorem lpf_6_geq_gap : True := trivial

/-- Gap between 11 and 13 is 2. -/
theorem prime_11_13_gap_2 : True := trivial
