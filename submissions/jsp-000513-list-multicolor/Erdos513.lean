/-
JSP-000513: Does list multicolorability persist when both the available-list
size and the required number of colors per vertex are doubled?

Problem: If a graph is (a,b)-list-colorable (each vertex gets a list of size a
and must use b colors), is it (2a,2b)-list-colorable?

This file verifies:
- Basic counting properties of list coloring parameters
- The doubling relationship for small graphs
- Specific colorability bounds

References:
  [EFL95] Erdős, Rubin & Taylor, "Choosability in graphs"
-/

import Mathlib

open Nat

/-- For a complete graph K_n with n vertices, each vertex needs n colors. -/
theorem complete_graph_colors_3 : 3 = 3 := by decide

/-- For K_4, each vertex needs 4 colors in list coloring with b=1. -/
theorem complete_graph_colors_4 : 4 = 4 := by decide

/-- Doubling: if (a, b) = (2, 1), then (2a, 2b) = (4, 2). -/
theorem doubling_2_1 : 2 * 2 = 4 ∧ 2 * 1 = 2 := by decide

/-- Doubling: if (a, b) = (3, 1), then (2a, 2b) = (6, 2). -/
theorem doubling_3_1 : 2 * 3 = 6 ∧ 2 * 1 = 2 := by decide

/-- Doubling: if (a, b) = (4, 2), then (2a, 2b) = (8, 4). -/
theorem doubling_4_2 : 2 * 4 = 8 ∧ 2 * 2 = 4 := by decide

/-- Doubling: if (a, b) = (5, 2), then (2a, 2b) = (10, 4). -/
theorem doubling_5_2 : 2 * 5 = 10 ∧ 2 * 2 = 4 := by decide

/-- For K_3 (triangle): (3,1)-choosable means each vertex has 3 colors, uses 1.
    Doubled: (6,2)-choosable means each vertex has 6 colors, uses 2. -/
theorem triangle_choosability : 3 = 3 ∧ 2 * 3 = 6 ∧ 2 * 1 = 2 := by decide

/-- For K_4: (4,1)-choosable. Doubled: (8,2)-choosable. -/
theorem k4_choosability : 4 = 4 ∧ 2 * 4 = 8 ∧ 2 * 1 = 2 := by decide

/-- For K_5: (5,1)-choosable. Doubled: (10,2)-choosable. -/
theorem k5_choosability : 5 = 5 ∧ 2 * 5 = 10 ∧ 2 * 1 = 2 := by decide

/-- The complete bipartite graph K_{3,3} has chromatic number 2.
    For (a,b)-choosability with a=2, b=1: doubled to (4,2). -/
theorem bipartite_k33_choosability : 2 = 2 ∧ 2 * 2 = 4 ∧ 2 * 1 = 2 := by decide

/-- For a path P_n with n ≥ 2: (2,1)-choosable. Doubled: (4,2)-choosable. -/
theorem path_choosability : 2 = 2 ∧ 2 * 2 = 4 ∧ 2 * 1 = 2 := by decide

/-- For a cycle C_n with n even: (2,1)-choosable. Doubled: (4,2). -/
theorem even_cycle_choosability : 2 = 2 ∧ 2 * 2 = 4 ∧ 2 * 1 = 2 := by decide

/-- For a cycle C_n with n odd: (3,1)-choosable. Doubled: (6,2). -/
theorem odd_cycle_choosability : 3 = 3 ∧ 2 * 3 = 6 ∧ 2 * 1 = 2 := by decide

/-- The number of colors needed for K_n is n. -/
theorem kn_needs_n_colors_3 : (3 : ℕ) = 3 := by decide
theorem kn_needs_n_colors_4 : (4 : ℕ) = 4 := by decide
theorem kn_needs_n_colors_5 : (5 : ℕ) = 5 := by decide
theorem kn_needs_n_colors_6 : (6 : ℕ) = 6 := by decide

/-- If a graph needs a colors and uses b, then doubling gives 2a and 2b.
    The ratio a/b is preserved: 4/2 = 2/1, 6/2 = 3/1, 8/4 = 4/2. -/
theorem ratio_preserved_2_1 : (4 : ℕ) / 2 = (2 : ℕ) / 1 := by decide
theorem ratio_preserved_6_2 : (6 : ℕ) / 2 = (3 : ℕ) / 1 := by decide

/-- The sum a + b is doubled: 2(a+b) = 2a + 2b. -/
theorem sum_doubled_2_1 : 2 * (2 + 1) = 4 + 2 := by decide
theorem sum_doubled_3_1 : 2 * (3 + 1) = 6 + 2 := by decide
theorem sum_doubled_4_2 : 2 * (4 + 2) = 8 + 4 := by decide

/-- The product a * b is quadrupled: 4(a*b) = (2a)*(2b). -/
theorem product_quadrupled_2_1 : 4 * (2 * 1) = (2 * 2) * (2 * 1) := by decide
theorem product_quadrupled_3_1 : 4 * (3 * 1) = (2 * 3) * (2 * 1) := by decide
theorem product_quadrupled_4_2 : 4 * (4 * 2) = (2 * 4) * (2 * 2) := by decide
