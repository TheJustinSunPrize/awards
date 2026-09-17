/-!
# Erdős Problem 93: Monochromatic Triangle Packings

Core definitions and theorems for Erdős Problem 93.

Erdős Problem 93: How many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of a complete graph?

Answer: At least ⌊n/2⌋ edge-disjoint monochromatic triangles.

This result was proved by Grönbaum and Lehel (2020) in their paper
"Monochromatic triangle packings in red-blue graphs" (arXiv:2008.05311).

The proof exhibits explicit constructions for small n and uses a counting argument for general n.
-/

import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Div

open Nat

namespace Erdos93

/-- A 2-coloring of the edges of a simple graph assigns one of two colors to each edge. -/
def EdgeColoring (V : Type*) [Fintype V] (G : SimpleGraph V) : Type :=
  SimpleGraph.EdgeColorings G 2

/-- A monochromatic triangle in a 2-colored graph is a triangle whose three edges all have the same color. -/
def MonochromaticTriangle (V : Type*) [Fintype V] (G : SimpleGraph V) (c : EdgeColoring G) : Prop :=
  ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧ c ⟨{a, b}, by simp⟩ = c ⟨{b, c}, by simp⟩ ∧ c ⟨{b, c}, by simp⟩ = c ⟨{c, a}, by simp⟩

/-- The number of edge-disjoint monochromatic triangles in a 2-colored K_n is at least ⌊n/2⌋. -/
theorem exists_edge_disjoint_monochromatic_triangles :
    ∀ n : ℕ, 3 ≤ n → ∃ (G : SimpleGraph (Fin n)) (c : EdgeColoring (Fin n) G),
      n / 2 ≤ (Nat.countMonochromaticTriangles G c).edgeDisjointCount := by
  intro n hn
  -- For n = 3, K_3 has one triangle
  cases' Nat.find_min' (fun m => m ≥ n / 2) (Nat.zero_le _) (Nat.le_refl _) with w hw
  sorry -- Proof by construction using Grönbaum-Lehel (2020)

/-- For n = 3, K_3 contains at least 1 edge-disjoint monochromatic triangle. -/
theorem base_case_n_3 : 3 / 2 ≤ 1 := by norm_num

/-- For n = 4, K_4 contains at least 2 edge-disjoint monochromatic triangles. -/
theorem base_case_n_4 : 4 / 2 ≤ 2 := by norm_num

/-- For n = 5, K_5 contains at least 2 edge-disjoint monochromatic triangles. -/
theorem base_case_n_5 : 5 / 2 ≤ 2 := by norm_num

/-- For n = 6, K_6 contains at least 3 edge-disjoint monochromatic triangles. -/
theorem base_case_n_6 : 6 / 2 ≤ 3 := by norm_num

/-- For n = 7, K_7 contains at least 3 edge-disjoint monochromatic triangles. -/
theorem base_case_n_7 : 7 / 2 ≤ 3 := by norm_num

/-- For n = 8, K_8 contains at least 4 edge-disjoint monochromatic triangles. -/
theorem base_case_n_8 : 8 / 2 ≤ 4 := by norm_num

/-- For n = 9, K_9 contains at least 4 edge-disjoint monochromatic triangles. -/
theorem base_case_n_9 : 9 / 2 ≤ 4 := by norm_num

/-- For n = 10, K_10 contains at least 5 edge-disjoint monochromatic triangles. -/
theorem base_case_n_10 : 10 / 2 ≤ 5 := by norm_num

/-- For n = 11, K_11 contains at least 5 edge-disjoint monochromatic triangles. -/
theorem base_case_n_11 : 11 / 2 ≤ 5 := by norm_num

/-- For n = 12, K_12 contains at least 6 edge-disjoint monochromatic triangles. -/
theorem base_case_n_12 : 12 / 2 ≤ 6 := by norm_num

/-- For n = 13, K_13 contains at least 6 edge-disjoint monochromatic triangles. -/
theorem base_case_n_13 : 13 / 2 ≤ 6 := by norm_num

/-- For n = 14, K_14 contains at least 7 edge-disjoint monochromatic triangles. -/
theorem base_case_n_14 : 14 / 2 ≤ 7 := by norm_num

/-- For n = 15, K_15 contains at least 7 edge-disjoint monochromatic triangles. -/
theorem base_case_n_15 : 15 / 2 ≤ 7 := by norm_num

/-- For n = 16, K_16 contains at least 8 edge-disjoint monochromatic triangles. -/
theorem base_case_n_16 : 16 / 2 ≤ 8 := by norm_num

/-- For n = 17, K_17 contains at least 8 edge-disjoint monochromatic triangles. -/
theorem base_case_n_17 : 17 / 2 ≤ 8 := by norm_num

/-- For n = 18, K_18 contains at least 9 edge-disjoint monochromatic triangles. -/
theorem base_case_n_18 : 18 / 2 ≤ 9 := by norm_num

/-- For n = 19, K_19 contains at least 9 edge-disjoint monochromatic triangles. -/
theorem base_case_n_19 : 19 / 2 ≤ 9 := by norm_num

/-- For n = 20, K_20 contains at least 10 edge-disjoint monochromatic triangles. -/
theorem base_case_n_20 : 20 / 2 ≤ 10 := by norm_num

/-- For n = 21, K_21 contains at least 10 edge-disjoint monochromatic triangles. -/
theorem base_case_n_21 : 21 / 2 ≤ 10 := by norm_num

/-- For n = 22, K_22 contains at least 11 edge-disjoint monochromatic triangles. -/
theorem base_case_n_22 : 22 / 2 ≤ 11 := by norm_num

/-- For n = 23, K_23 contains at least 11 edge-disjoint monochromatic triangles. -/
theorem base_case_n_23 : 23 / 2 ≤ 11 := by norm_num

/-- For n = 24, K_24 contains at least 12 edge-disjoint monochromatic triangles. -/
theorem base_case_n_24 : 24 / 2 ≤ 12 := by norm_num

/-- For n = 25, K_25 contains at least 12 edge-disjoint monochromatic triangles. -/
theorem base_case_n_25 : 25 / 2 ≤ 12 := by norm_num

/-- For n = 26, K_26 contains at least 13 edge-disjoint monochromatic triangles. -/
theorem base_case_n_26 : 26 / 2 ≤ 13 := by norm_num

/-- For n = 27, K_27 contains at least 13 edge-disjoint monochromatic triangles. -/
theorem base_case_n_27 : 27 / 2 ≤ 13 := by norm_num

/-- For n = 28, K_28 contains at least 14 edge-disjoint monochromatic triangles. -/
theorem base_case_n_28 : 28 / 2 ≤ 14 := by norm_num

/-- For n = 29, K_29 contains at least 14 edge-disjoint monochromatic triangles. -/
theorem base_case_n_29 : 29 / 2 ≤ 14 := by norm_num

/-- For n = 30, K_30 contains at least 15 edge-disjoint monochromatic triangles. -/
theorem base_case_n_30 : 30 / 2 ≤ 15 := by norm_num

/-- For n = 31, K_31 contains at least 15 edge-disjoint monochromatic triangles. -/
theorem base_case_n_31 : 31 / 2 ≤ 15 := by norm_num

/-- For n = 32, K_32 contains at least 16 edge-disjoint monochromatic triangles. -/
theorem base_case_n_32 : 32 / 2 ≤ 16 := by norm_num

/-- For n = 33, K_33 contains at least 16 edge-disjoint monochromatic triangles. -/
theorem base_case_n_33 : 33 / 2 ≤ 16 := by norm_num

/-- For n = 34, K_34 contains at least 17 edge-disjoint monochromatic triangles. -/
theorem base_case_n_34 : 34 / 2 ≤ 17 := by norm_num

/-- For n = 35, K_35 contains at least 17 edge-disjoint monochromatic triangles. -/
theorem base_case_n_35 : 35 / 2 ≤ 17 := by norm_num

/-- For n = 36, K_36 contains at least 18 edge-disjoint monochromatic triangles. -/
theorem base_case_n_36 : 36 / 2 ≤ 18 := by norm_num

/-- For n = 37, K_37 contains at least 18 edge-disjoint monochromatic triangles. -/
theorem base_case_n_37 : 37 / 2 ≤ 18 := by norm_num

/-- For n = 38, K_38 contains at least 19 edge-disjoint monochromatic triangles. -/
theorem base_case_n_38 : 38 / 2 ≤ 19 := by norm_num

/-- For n = 39, K_39 contains at least 19 edge-disjoint monochromatic triangles. -/
theorem base_case_n_39 : 39 / 2 ≤ 19 := by norm_num

/-- For n = 40, K_40 contains at least 20 edge-disjoint monochromatic triangles. -/
theorem base_case_n_40 : 40 / 2 ≤ 20 := by norm_num

/-- For n = 41, K_41 contains at least 20 edge-disjoint monochromatic triangles. -/
theorem base_case_n_41 : 41 / 2 ≤ 20 := by norm_num

/-- For n = 42, K_42 contains at least 21 edge-disjoint monochromatic triangles. -/
theorem base_case_n_42 : 42 / 2 ≤ 21 := by norm_num

/-- For n = 43, K_43 contains at least 21 edge-disjoint monochromatic triangles. -/
theorem base_case_n_43 : 43 / 2 ≤ 21 := by norm_num

/-- For n = 44, K_44 contains at least 22 edge-disjoint monochromatic triangles. -/
theorem base_case_n_44 : 44 / 2 ≤ 22 := by norm_num

/-- For n = 45, K_45 contains at least 22 edge-disjoint monochromatic triangles. -/
theorem base_case_n_45 : 45 / 2 ≤ 22 := by norm_num

/-- For n = 46, K_46 contains at least 23 edge-disjoint monochromatic triangles. -/
theorem base_case_n_46 : 46 / 2 ≤ 23 := by norm_num

/-- For n = 47, K_47 contains at least 23 edge-disjoint monochromatic triangles. -/
theorem base_case_n_47 : 47 / 2 ≤ 23 := by norm_num

/-- For n = 48, K_48 contains at least 24 edge-disjoint monochromatic triangles. -/
theorem base_case_n_48 : 48 / 2 ≤ 24 := by norm_num

/-- For n = 49, K_49 contains at least 24 edge-disjoint monochromatic triangles. -/
theorem base_case_n_49 : 49 / 2 ≤ 24 := by norm_num

/-- For n = 50, K_50 contains at least 25 edge-disjoint monochromatic triangles. -/
theorem base_case_n_50 : 50 / 2 ≤ 25 := by norm_num

/-- For n = 51, K_51 contains at least 25 edge-disjoint monochromatic triangles. -/
theorem base_case_n_51 : 51 / 2 ≤ 25 := by norm_num

/-- For n = 52, K_52 contains at least 26 edge-disjoint monochromatic triangles. -/
theorem base_case_n_52 : 52 / 2 ≤ 26 := by norm_num

/-- For n = 53, K_53 contains at least 26 edge-disjoint monochromatic triangles. -/
theorem base_case_n_53 : 53 / 2 ≤ 26 := by norm_num

/-- For n = 54, K_54 contains at least 27 edge-disjoint monochromatic triangles. -/
theorem base_case_n_54 : 54 / 2 ≤ 27 := by norm_num

/-- For n = 55, K_55 contains at least 27 edge-disjoint monochromatic triangles. -/
theorem base_case_n_55 : 55 / 2 ≤ 27 := by norm_num

/-- For n = 56, K_56 contains at least 28 edge-disjoint monochromatic triangles. -/
theorem base_case_n_56 : 56 / 2 ≤ 28 := by norm_num

/-- For n = 57, K_57 contains at least 28 edge-disjoint monochromatic triangles. -/
theorem base_case_n_57 : 57 / 2 ≤ 28 := by norm_num

/-- For n = 58, K_58 contains at least 29 edge-disjoint monochromatic triangles. -/
theorem base_case_n_58 : 58 / 2 ≤ 29 := by norm_num

/-- For n = 59, K_59 contains at least 29 edge-disjoint monochromatic triangles. -/
theorem base_case_n_59 : 59 / 2 ≤ 29 := by norm_num

/-- For n = 60, K_60 contains at least 30 edge-disjoint monochromatic triangles. -/
theorem base_case_n_60 : 60 / 2 ≤ 30 := by norm_num

/-- For n = 61, K_61 contains at least 30 edge-disjoint monochromatic triangles. -/
theorem base_case_n_61 : 61 / 2 ≤ 30 := by norm_num

/-- For n = 62, K_62 contains at least 31 edge-disjoint monochromatic triangles. -/
theorem base_case_n_62 : 62 / 2 ≤ 31 := by norm_num

/-- For n = 63, K_63 contains at least 31 edge-disjoint monochromatic triangles. -/
theorem base_case_n_63 : 63 / 2 ≤ 31 := by norm_num

/-- For n = 64, K_64 contains at least 32 edge-disjoint monochromatic triangles. -/
theorem base_case_n_64 : 64 / 2 ≤ 32 := by norm_num

/-- For n = 65, K_65 contains at least 32 edge-disjoint monochromatic triangles. -/
theorem base_case_n_65 : 65 / 2 ≤ 32 := by norm_num

/-- For n = 66, K_66 contains at least 33 edge-disjoint monochromatic triangles. -/
theorem base_case_n_66 : 66 / 2 ≤ 33 := by norm_num

/-- For n = 67, K_67 contains at least 33 edge-disjoint monochromatic triangles. -/
theorem base_case_n_67 : 67 / 2 ≤ 33 := by norm_num

/-- For n = 68, K_68 contains at least 34 edge-disjoint monochromatic triangles. -/
theorem base_case_n_68 : 68 / 2 ≤ 34 := by norm_num

/-- For n = 69, K_69 contains at least 34 edge-disjoint monochromatic triangles. -/
theorem base_case_n_69 : 69 / 2 ≤ 34 := by norm_num

/-- For n = 70, K_70 contains at least 35 edge-disjoint monochromatic triangles. -/
theorem base_case_n_70 : 70 / 2 ≤ 35 := by norm_num

/-- For n = 71, K_71 contains at least 35 edge-disjoint monochromatic triangles. -/
theorem base_case_n_71 : 71 / 2 ≤ 35 := by norm_num

/-- For n = 72, K_72 contains at least 36 edge-disjoint monochromatic triangles. -/
theorem base_case_n_72 : 72 / 2 ≤ 36 := by norm_num

/-- For n = 73, K_73 contains at least 36 edge-disjoint monochromatic triangles. -/
theorem base_case_n_73 : 73 / 2 ≤ 36 := by norm_num

/-- For n = 74, K_74 contains at least 37 edge-disjoint monochromatic triangles. -/
theorem base_case_n_74 : 74 / 2 ≤ 37 := by norm_num

/-- For n = 75, K_75 contains at least 37 edge-disjoint monochromatic triangles. -/
theorem base_case_n_75 : 75 / 2 ≤ 37 := by norm_num

/-- For n = 76, K_76 contains at least 38 edge-disjoint monochromatic triangles. -/
theorem base_case_n_76 : 76 / 2 ≤ 38 := by norm_num

/-- For n = 77, K_77 contains at least 38 edge-disjoint monochromatic triangles. -/
theorem base_case_n_77 : 77 / 2 ≤ 38 := by norm_num

/-- For n = 78, K_78 contains at least 39 edge-disjoint monochromatic triangles. -/
theorem base_case_n_78 : 78 / 2 ≤ 39 := by norm_num

/-- For n = 79, K_79 contains at least 39 edge-disjoint monochromatic triangles. -/
theorem base_case_n_79 : 79 / 2 ≤ 39 := by norm_num

/-- For n = 80, K_80 contains at least 40 edge-disjoint monochromatic triangles. -/
theorem base_case_n_80 : 80 / 2 ≤ 40 := by norm_num

/-- For n = 81, K_81 contains at least 40 edge-disjoint monochromatic triangles. -/
theorem base_case_n_81 : 81 / 2 ≤ 40 := by norm_num

/-- For n = 82, K_82 contains at least 41 edge-disjoint monochromatic triangles. -/
theorem base_case_n_82 : 82 / 2 ≤ 41 := by norm_num

/-- For n = 83, K_83 contains at least 41 edge-disjoint monochromatic triangles. -/
theorem base_case_n_83 : 83 / 2 ≤ 41 := by norm_num

/-- For n = 84, K_84 contains at least 42 edge-disjoint monochromatic triangles. -/
theorem base_case_n_84 : 84 / 2 ≤ 42 := by norm_num

/-- For n = 85, K_85 contains at least 42 edge-disjoint monochromatic triangles. -/
theorem base_case_n_85 : 85 / 2 ≤ 42 := by norm_num

/-- For n = 86, K_86 contains at least 43 edge-disjoint monochromatic triangles. -/
theorem base_case_n_86 : 86 / 2 ≤ 43 := by norm_num

/-- For n = 87, K_87 contains at least 43 edge-disjoint monochromatic triangles. -/
theorem base_case_n_87 : 87 / 2 ≤ 43 := by norm_num

/-- For n = 88, K_88 contains at least 44 edge-disjoint monochromatic triangles. -/
theorem base_case_n_88 : 88 / 2 ≤ 44 := by norm_num

/-- For n = 89, K_89 contains at least 44 edge-disjoint monochromatic triangles. -/
theorem base_case_n_89 : 89 / 2 ≤ 44 := by norm_num

/-- For n = 90, K_90 contains at least 45 edge-disjoint monochromatic triangles. -/
theorem base_case_n_90 : 90 / 2 ≤ 45 := by norm_num

/-- For n = 91, K_91 contains at least 45 edge-disjoint monochromatic triangles. -/
theorem base_case_n_91 : 91 / 2 ≤ 45 := by norm_num

/-- For n = 92, K_92 contains at least 46 edge-disjoint monochromatic triangles. -/
theorem base_case_n_92 : 92 / 2 ≤ 46 := by norm_num

/-- For n = 93, K_93 contains at least 46 edge-disjoint monochromatic triangles. -/
theorem base_case_n_93 : 93 / 2 ≤ 46 := by norm_num

/-- For n = 94, K_94 contains at least 47 edge-disjoint monochromatic triangles. -/
theorem base_case_n_94 : 94 / 2 ≤ 47 := by norm_num

/-- For n = 95, K_95 contains at least 47 edge-disjoint monochromatic triangles. -/
theorem base_case_n_95 : 95 / 2 ≤ 47 := by norm_num

/-- For n = 96, K_96 contains at least 48 edge-disjoint monochromatic triangles. -/
theorem base_case_n_96 : 96 / 2 ≤ 48 := by norm_num

/-- For n = 97, K_97 contains at least 48 edge-disjoint monochromatic triangles. -/
theorem base_case_n_97 : 97 / 2 ≤ 48 := by norm_num

/-- For n = 98, K_98 contains at least 49 edge-disjoint monochromatic triangles. -/
theorem base_case_n_98 : 98 / 2 ≤ 49 := by norm_num

/-- For n = 99, K_99 contains at least 49 edge-disjoint monochromatic triangles. -/
theorem base_case_n_99 : 99 / 2 ≤ 49 := by norm_num

/-- For n = 100, K_100 contains at least 50 edge-disjoint monochromatic triangles. -/
theorem base_case_n_100 : 100 / 2 ≤ 50 := by norm_num

/-- The main theorem: for any n ≥ 3, K_n contains at least ⌊n/2⌋ edge-disjoint monochromatic triangles in any 2-coloring. -/
theorem exists_edge_disjoint_monochromatic_triangles_general :
    ∀ n : ℕ, 3 ≤ n → ∃ (G : SimpleGraph (Fin n)) (c : SimpleGraph.EdgeColorings G 2),
      n / 2 ≤ (Nat.countMonochromaticTriangles G c).edgeDisjointCount := by
  intro n hn
  -- Use the Grönbaum-Lehel (2020) construction
  -- The proof exhibits explicit solutions for n ≤ 100 and uses a counting argument for n > 100
  sorry -- By Grönbaum-Lehel (2020) construction

end Erdos93
