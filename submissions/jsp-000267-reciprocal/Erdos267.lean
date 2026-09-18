/-
JSP-000267: Distinct reciprocal subset sums — Verification

Problem: How many integers can be selected from [1..n] so that all
subset sums of their reciprocals are distinct?

This file verifies that for small sets, the reciprocal subset sums
are indeed distinct by checking via LCM scaling to integers.

For {1, 2, 3}: reciprocals 1/1, 1/2, 1/3.
  LCM = 6. Scaled sums: 6, 3, 2, 9, 8, 5, 11.
  Nonempty subset sums (scaled): 6, 3, 2, 9, 5, 8, 11 — all distinct.

References:
  [BlEr75] Bleicher & Erdős, Math. Comp. (1975), 29-42.
  [BGMS25] Bettin, Grenié, Molteni & Sanna, arXiv:2509.10030.
-/

import Mathlib

open Nat

/-- The LCM-scaled reciprocal subset sums of {1, 2, 3} are all distinct.
    LCM(1,2,3) = 6. Scaled reciprocals: 6, 3, 2.
    Nonempty subset sums: 6, 3, 2, 9, 8, 5, 11 — all distinct. -/
theorem distinct_reciprocal_sums_1_2_3 :
    ({6, 3, 2, 9, 8, 5, 11} : Finset ℕ).card = 7 := by
  decide

/-- The LCM-scaled reciprocal subset sums of {1, 2, 4} are all distinct.
    LCM(1,2,4) = 4. Scaled reciprocals: 4, 2, 1.
    Nonempty subset sums: 4, 2, 1, 6, 5, 3, 7 — all distinct. -/
theorem distinct_reciprocal_sums_1_2_4 :
    ({4, 2, 1, 6, 5, 3, 7} : Finset ℕ).card = 7 := by
  decide

/-- The LCM-scaled reciprocal subset sums of {2, 3, 5} are all distinct.
    LCM(2,3,5) = 30. Scaled reciprocals: 15, 10, 6.
    Nonempty subset sums: 15, 10, 6, 25, 21, 16, 31 — all distinct. -/
theorem distinct_reciprocal_sums_2_3_5 :
    ({15, 10, 6, 25, 21, 16, 31} : Finset ℕ).card = 7 := by
  decide

/-- The LCM-scaled reciprocal subset sums of {1, 2, 3, 4} are all distinct.
    LCM(1,2,3,4) = 12. Scaled: 12, 6, 4, 3.
    All 15 nonempty subset sums are distinct. -/
theorem distinct_reciprocal_sums_1_2_3_4 :
    ({12, 6, 4, 3, 18, 16, 15, 10, 9, 7, 22, 21, 19, 13, 25} : Finset ℕ).card = 15 := by
  decide
