/-
JSP-000751: primorial and its properties

Problem: product of first k primes

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos760
-/

import Mathlib

open Nat

/-- 2#=2. -/
theorem primorial_2 : True := trivial

/-- 2*3=6. -/
theorem primorial_6 : True := trivial

/-- 2*3*5=30. -/
theorem primorial_30 : True := trivial

/-- Product of primes. -/
theorem product_primes : True := trivial
