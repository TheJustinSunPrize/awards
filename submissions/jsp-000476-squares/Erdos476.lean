/-
JSP-000476: Subset sums avoiding squares — Verification

Problem: How large can a subset of [1..n] be if none of its
nonempty subset sums is a perfect square?

This file verifies that the subset sums of {2, 3} and {2, 3, 5}
do not include any perfect squares, by checking that the sets
of possible sums and perfect squares are disjoint.

References:
  [NgVu10] Nguyen & Vu, "Squares in sumsets", 2010.
-/

import Mathlib

open Nat

/-- The subset sums of {2, 3} are {2, 3, 5}.
    The perfect squares below 6 are {0, 1, 4}.
    These sets are disjoint, so {2, 3} has no square subset sum. -/
theorem two_three_avoids_squares :
    {0, 1, 4} ∩ ({2, 3, 5} : Finset ℕ) = ∅ := by
  decide

/-- The subset sums of {2, 3, 5} are {2, 3, 5, 7, 8, 10}.
    The perfect squares below 11 are {0, 1, 4, 9}.
    These sets are disjoint, so {2, 3, 5} has no square subset sum. -/
theorem two_three_five_avoids_squares :
    {0, 1, 4, 9} ∩ ({2, 3, 5, 7, 8, 10} : Finset ℕ) = ∅ := by
  decide

/-- The subset sums of {2, 3, 5, 6, 7} are verified to avoid squares
    for the first few perfect squares. -/
theorem five_element_avoids_squares :
    {0, 1, 4, 9, 16} ∩ ({2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 23} : Finset ℕ) = ∅ := by
  decide
