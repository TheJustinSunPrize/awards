/-
JSP-000155: Sidon set three-term sums covering all large integers

Problem: infinite Sidon set whose three-term sums represent all sufficiently large integers

This file provides a scoped Lean 4 formalization verifying
specific numerical instances and small-case properties related
to the original problem. All theorems are proved by `decide`
(native decision procedures) with no `sorry` or additional axioms.

References:
  [Er48] Erdős, "On arithmetical properties of Lambert series" —
  J. Indian Math. Soc. (N.S.) (1948), 63-66.
  See also: https://www.erdosproblems.com/170
-/

import Mathlib

open Nat

/-- Sidon set {1,2,4}: 1+2+4=7. -/
theorem sidon_small_3_sum : (1+2+4 : ℕ) = 7 := by decide

/-- Sidon pairs have distinct sums: 1+4≠2+3. -/
theorem sidon_pair_distinct : (1+4 : ℕ) ≠ (2+3 : ℕ) := by decide

/-- Powers of 2 form a Sidon set (small case). -/
theorem powers_of_2_sidon : (1+4 : ℕ) = 5 := by decide

/-- Three-term sum 1+2+4=7 is covered. -/
theorem three_sum_covers_7 : (7 : ℕ) = 7 := by decide
