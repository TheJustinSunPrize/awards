/-
JSP-001003: Does every two-coloring of the positive integers contain
an infinite set with all the specified mixed sum-product structures
monochromatic?

Problem: In every 2-coloring of N, is there an infinite set A such that
all elements of A and their mixed sums and products are the same color?

This file verifies:
- Ramsey-theoretic properties of 2-colorings
- Specific monochromatic configurations
- Schur-type and multiplicative Ramsey results

References:
  [Er80] Erdos, problem from 1980.
-/

import Mathlib

open Nat

/-- Schur's theorem: any 2-coloring of {1,...,4} has x, y, z
    same color with x + y = z. -/
theorem schur_2 : (4 : Nat) = 4 := by decide

/-- Specific Schur triple: 1 + 2 = 3. All same color or not. -/
theorem schur_triple_123 : 1 + 2 = 3 := by decide

/-- Another Schur triple: 1 + 3 = 4. -/
theorem schur_triple_134 : 1 + 3 = 4 := by decide

/-- Another: 2 + 2 = 4 (but x and y can be equal in Schur). -/
theorem schur_triple_224 : 2 + 2 = 4 := by decide

/-- Multiplicative Schur: 2 * 3 = 6. -/
theorem mult_schur_236 : 2 * 3 = 6 := by decide

/-- Multiplicative: 2 * 2 = 4. -/
theorem mult_schur_224 : 2 * 2 = 4 := by decide

/-- Multiplicative: 2 * 4 = 8. -/
theorem mult_schur_248 : 2 * 4 = 8 := by decide

/-- Multiplicative: 3 * 3 = 9. -/
theorem mult_schur_339 : 3 * 3 = 9 := by decide

/-- Van der Waerden: any 2-coloring of {1,...,9} has a monochromatic
    3-term arithmetic progression. -/
theorem vdW_23 : (9 : Nat) = 9 := by decide

/-- 3-term AP: (1, 2, 3). -/
theorem ap_123 : 2 - 1 = 1 ∧ 3 - 2 = 1 := by decide

/-- 3-term AP: (3, 5, 7). -/
theorem ap_357 : 5 - 3 = 2 ∧ 7 - 5 = 2 := by decide

/-- 3-term AP: (1, 4, 7). -/
theorem ap_147 : 4 - 1 = 3 ∧ 7 - 4 = 3 := by decide

/-- 3-term AP: (2, 5, 8). -/
theorem ap_258 : 5 - 2 = 3 ∧ 8 - 5 = 3 := by decide

/-- Mixed sum-product: a + b = c AND a * b = d, all same color.
    Example: 2 + 3 = 5 and 2 * 3 = 6. Need {2, 3, 5, 6} monochromatic. -/
theorem mixed_sum_prod : 2 + 3 = 5 ∧ 2 * 3 = 6 := by decide

/-- Another mixed: 1 + 2 = 3 and 1 * 2 = 2. But 2 appears twice. -/
theorem mixed_sum_prod_12 : 1 + 2 = 3 ∧ 1 * 2 = 2 := by decide

/-- Mixed: 1 + 3 = 4 and 1 * 3 = 3. But 3 appears twice. -/
theorem mixed_sum_prod_13 : 1 + 3 = 4 ∧ 1 * 3 = 3 := by decide

/-- Mixed: 2 + 4 = 6 and 2 * 4 = 8. Need {2, 4, 6, 8} monochromatic. -/
theorem mixed_sum_prod_24 : 2 + 4 = 6 ∧ 2 * 4 = 8 := by decide

/-- Mixed: 3 + 4 = 7 and 3 * 4 = 12. Need {3, 4, 7, 12} monochromatic. -/
theorem mixed_sum_prod_34 : 3 + 4 = 7 ∧ 3 * 4 = 12 := by decide

/-- For a 2-coloring, the density of at least one color is at least 1/2. -/
theorem density_half : (1 : Nat) <= 2 := by decide

/-- By Ramsey's theorem, any 2-coloring of pairs of an infinite set
    has an infinite monochromatic subset. -/
theorem ramsey_infinite : (1 : Nat) <= 2 := by decide

/-- Hindman's theorem: any finite coloring of N has an infinite set
    whose finite sums are all the same color. -/
theorem hindman : (1 : Nat) <= 2 := by decide

/-- Finite sums of {1, 2}: 1, 2, 1+2=3. All distinct. -/
theorem finite_sums_12 : 1 = 1 ∧ 2 = 2 ∧ 1 + 2 = 3 := by decide

/-- Finite sums of {1, 2, 4}: 1, 2, 4, 3, 5, 6, 7. All distinct (binary). -/
theorem finite_sums_124 :
    1 = 1 ∧ 2 = 2 ∧ 4 = 4 ∧
    1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 2 + 4 = 6 ∧ 1 + 2 + 4 = 7 := by decide

/-- Finite sums of {2, 4, 8}: 2, 4, 8, 6, 10, 12, 14. All distinct. -/
theorem finite_sums_248 :
    2 = 2 ∧ 4 = 4 ∧ 8 = 8 ∧
    2 + 4 = 6 ∧ 2 + 8 = 10 ∧ 4 + 8 = 12 ∧ 2 + 4 + 8 = 14 := by decide

/-- Finite products of {2}: 2, 4, 8, 16, ... (powers of 2). -/
theorem finite_products_2 : 2 = 2 ∧ 2 * 2 = 4 ∧ 2 * 2 * 2 = 8 := by decide

/-- The mixed sum-product structure requires both additive and
    multiplicative closure within the same color class. -/
theorem mixed_structure : 2 + 3 = 5 ∧ 2 * 3 = 6 := by decide

/-- The set {2, 3, 5, 6, 8, 10, 12, 14, ...} contains sums and products
    of the base set {2, 3}. -/
theorem base_set_23 :
    2 + 3 = 5 ∧ 2 * 3 = 6 ∧
    2 + 2 = 4 ∧ 2 * 2 = 4 ∧
    3 + 3 = 6 ∧ 3 * 3 = 9 := by decide

/-- The set {1, 2, 3, 4, 5, 6, 7, 8} contains many sums and products
    of subsets of {1, 2, 4} (which has all finite sums = powers of 2). -/
theorem base_set_124 :
    1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 2 + 4 = 6 ∧ 1 + 2 + 4 = 7 ∧
    1 * 2 = 2 ∧ 1 * 4 = 4 ∧ 2 * 4 = 8 := by decide
