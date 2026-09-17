import ErdosProblems.Erdos307
import ErdosProblems.Erdos52
import ErdosProblems.Erdos93

/-!
# Erdős Problems

This file collects all Lean formalizations of solutions to Erdős problems.
-/

namespace ErdosProblems

/-- Formalization of Erdős Problem 307. -/
theorem erdos_307 : ∃ n : ℕ, 1 < n ∧ lpf n > lpf (n + 1) ∧ lpf (n + 1) > lpf (n + 2) :=
  Erdos307.exists_three_consecutive_decreasing_lpf

/-- Formalization of Erdős Problem 52. -/
theorem erdos_52 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ d n = d (n + 1) :=
  Erdos52.exists_infinitely_many_consecutive_equal_d

/-- Formalization of Erdős Problem 93. -/
theorem erdos_93 : ∀ n : ℕ, 3 ≤ n → ∃ (G : SimpleGraph (Fin n)) (c : SimpleGraph.EdgeColorings G 2), n / 2 ≤ (Nat.countMonochromaticTriangles G c).edgeDisjointCount :=
  Erdos93.exists_edge_disjoint_monochromatic_triangles_general

end ErdosProblems
