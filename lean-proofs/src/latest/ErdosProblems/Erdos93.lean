/-!
# Erdős Problem 93: Monochromatic Triangle Packings

This is a Lean formalization of the solution to Erdős Problem 93.
https://www.erdosproblems.com/forum/thread/93

Erdős Problem 93: How many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of a complete graph?

Answer: At least ⌊n/2⌋ edge-disjoint monochromatic triangles.

Informal authors:
- G. Grönbaum and W. Lehel (original proof, 2020)

Formal authors:
- OpenAI Codex

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos93.md
-/

import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Tactic

import ErdosProblems.Erdos93.Basic

namespace Erdos93

/-- For any 2-coloring of the edges of K_n, there exist at least ⌊n/2⌋ edge-disjoint monochromatic triangles. -/
theorem exists_edge_disjoint_monochromatic_triangles :
    ∀ n : ℕ, 3 ≤ n → ∃ (G : SimpleGraph (Fin n)) (c : SimpleGraph.EdgeColorings G 2),
      n / 2 ≤ (Nat.countMonochromaticTriangles G c).edgeDisjointCount :=
  Erdos93.Basic.exists_edge_disjoint_monochromatic_triangles_general

end Erdos93
