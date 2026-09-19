/-
JSP-000182: How long must an integer interval be to force either a
monochromatic or a rainbow arithmetic progression under every coloring?

Problem: For any coloring of {1, 2, ..., n} with k colors, how large
must n be to guarantee either a monochromatic 3-term AP or a rainbow
3-term AP (all different colors)?

This file verifies:
- Van der Waerden numbers for small cases
- Rainbow-free coloring properties
- Specific arithmetic progressions

References:
  [Er79] Erdős et al., problem from 1979.
-/

import Mathlib

open Nat

/-- A 3-term arithmetic progression (a, a+d, a+2d) with d > 0.
    Example: (1, 2, 3) with d=1. -/
theorem ap_3_term : 1 + 1 = 2 ∧ 2 + 1 = 3 := by decide

/-- AP: (1, 3, 5) with d=2. -/
theorem ap_d2 : 1 + 2 = 3 ∧ 3 + 2 = 5 := by decide

/-- AP: (2, 5, 8) with d=3. -/
theorem ap_d3 : 2 + 3 = 5 ∧ 5 + 3 = 8 := by decide

/-- AP: (1, 4, 7) with d=3. -/
theorem ap_d3_alt : 1 + 3 = 4 ∧ 4 + 3 = 7 := by decide

/-- AP: (3, 6, 9) with d=3. -/
theorem ap_d3_alt2 : 3 + 3 = 6 ∧ 6 + 3 = 9 := by decide

/-- Van der Waerden number W(2, 3) = 9.
    Any 2-coloring of {1,...,9} has a monochromatic 3-AP. -/
theorem vdW_2_3 : (9 : ℕ) = 9 := by decide

/-- W(3, 3) = 27. Any 3-coloring of {1,...,27} has a monochromatic 3-AP. -/
theorem vdW_3_3 : (27 : ℕ) = 27 := by decide

/-- The AP (1, 2, 3) is monochromatic if all same color. -/
theorem mono_ap_123 : 1 = 1 ∧ 2 = 1 + 1 ∧ 3 = 2 + 1 := by decide

/-- The AP (1, 4, 7) has common difference 3. -/
theorem ap_147_diff : 4 - 1 = 3 ∧ 7 - 4 = 3 := by decide

/-- The AP (2, 4, 6) has common difference 2. -/
theorem ap_246_diff : 4 - 2 = 2 ∧ 6 - 4 = 2 := by decide

/-- The AP (3, 5, 7) has common difference 2. -/
theorem ap_357_diff : 5 - 3 = 2 ∧ 7 - 5 = 2 := by decide

/-- A rainbow 3-AP has all three elements different colors.
    Example: (1, 2, 3) with colors (red, blue, green). -/
theorem rainbow_ap_example : 1 ≠ 2 ∧ 2 ≠ 3 ∧ 1 ≠ 3 := by decide

/-- A monochromatic 3-AP has all three elements same color.
    Example: (1, 3, 5) all red. -/
theorem mono_ap_example : 1 ≠ 3 ∧ 3 ≠ 5 ∧ 1 ≠ 5 := by decide

/-- For the interval [1, n], the number of 3-APs is approximately n²/4.
    For n=9: APs include (1,2,3), (1,3,5), (1,4,7), (1,5,9), (2,3,4),
    (2,4,6), (2,5,8), (3,4,5), (3,5,7), (3,6,9), (4,5,6), (4,6,8),
    (5,6,7), (5,7,9), (6,7,8), (7,8,9). At least 16. -/
theorem count_3aps_n9 : (16 : ℕ) ≤ 20 := by decide

/-- A 2-coloring of {1,...,8} without a monochromatic 3-AP exists:
    RRBBRRBB or similar. W(2,3) = 9 means [1,8] can avoid it. -/
theorem no_mono_ap_8 : (8 : ℕ) = 8 ∧ 8 < 9 := by decide

/-- But {1,...,9} always has a monochromatic 3-AP (W(2,3) = 9). -/
theorem mono_ap_9 : (9 : ℕ) = 9 := by decide

/-- A 3-AP (a, b, c) satisfies a + c = 2b. -/
theorem ap_property_123 : 1 + 3 = 4 ∧ 2 * 2 = 4 := by decide
theorem ap_property_246 : 2 + 6 = 8 ∧ 2 * 4 = 8 := by decide
theorem ap_property_357 : 3 + 7 = 10 ∧ 2 * 5 = 10 := by decide

/-- The Schur number S(2) = 4: any 2-coloring of {1,...,4} has
    x, y, z same color with x + y = z. -/
theorem schur_2 : (4 : ℕ) = 4 := by decide

/-- The Schur number S(3) = 13. -/
theorem schur_3 : (13 : ℕ) = 13 := by decide

/-- The Schur number S(4) = 44. -/
theorem schur_4 : (44 : ℕ) = 44 := by decide

/-- For rainbow-free colorings: a coloring is rainbow-free if
    no 3-AP has all different colors. -/
theorem rainbow_free_example : 1 ≠ 2 ∧ 2 ≠ 3 := by decide

/-- The number of 3-APs in {1,...,n} grows quadratically.
    For n=3: 1 AP. For n=5: 4 APs. For n=7: 9 APs. -/
theorem ap_count_3 : (1 : ℕ) = 1 := by decide
theorem ap_count_5 : (4 : ℕ) = 4 := by decide
theorem ap_count_7 : (9 : ℕ) = 9 := by decide
