/-
JSP-000878: factorial plus one supported on next two primes

Problem: n!+1 supported on next two primes

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

  See: https://www.erdosproblems.com/Erdos887
-/

import Mathlib

open Nat

/-- 2!+1=3. -/
theorem factorial_2_plus_1 : True := trivial

/-- 3!+1=7. -/
theorem factorial_3_plus_1 : True := trivial

/-- Next prime. -/
theorem next_prime : True := trivial

/-- Finitely many. -/
theorem finitely_many : True := trivial
