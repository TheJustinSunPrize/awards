import FCC.ContactGraph
import FCC.Counting
import FCC.Scale

namespace FCC

/-- The exact number of unordered unit-distance contacts in the real FCC box. -/
theorem exact_contacts (m : ℕ) :
    (contactGraph m).edgeFinset.card = 6*m*(2*m-1)^2 := by
  rw [contactGraph_edge_card, contactPairs_card]

/-- Adding isolated, well-separated points preserves every contact exactly. -/
theorem exact_padded_contacts (m q : ℕ) :
    (paddedContactGraph m q).edgeFinset.card = 6*m*(2*m-1)^2 := by
  rw [paddedContactGraph_edge_card, contactPairs_card]

/-- A constructive lower bound for every cardinality, with an explicit
nonoptimal constant. The graph counts actual unordered Euclidean contacts. -/
theorem all_cardinalities (n : ℕ) (hn : 4 ≤ n) :
    ∃ m q : ℕ,
      Fintype.card (Vertex m ⊕ Fin q) = n ∧
      Function.Injective (@paddedPoint m q) ∧
      (∀ u v : Vertex m ⊕ Fin q, u ≠ v →
        1 ≤ dist (paddedPoint u) (paddedPoint v)) ∧
      6*(n : ℝ) - 200*(n : ℝ)^(2/3 : ℝ) ≤
        ((paddedContactGraph m q).edgeFinset.card : ℝ) := by
  obtain ⟨m, hm, hlo, hhi⟩ := exists_box_scale n hn
  refine ⟨m, n-4*m^3, ?_, paddedPoint_injective, ?_, ?_⟩
  · simp only [Fintype.card_sum, vertex_card, Fintype.card_fin]
    omega
  · intro u v h
    exact paddedPoint_separated h
  · rw [exact_padded_contacts]
    exact contact_count_lower_bound hm hlo hhi

end FCC
