import TrianglePacking.Basic

namespace TrianglePacking

open Finset

theorem vertex_card (r s : ℕ) : Fintype.card (Vertex r s) = 2 * r + s := by
  simp [Vertex]
  omega

theorem degree_left (r s : ℕ) (a : Fin r) :
    (graph r s).degree (.inl (.inl a)) = r + s := by
  have hn : (graph r s).neighborFinset (.inl (.inl a)) =
      ((∅ : Finset (Fin r)).disjSum (univ : Finset (Fin r))).disjSum
        (univ : Finset (Fin s)) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    rcases v with (v | v) | v <;>
      simp [graph, part, Fin.ext_iff]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
  simp

theorem degree_right (r s : ℕ) (b : Fin r) :
    (graph r s).degree (.inl (.inr b)) = r + s := by
  have hn : (graph r s).neighborFinset (.inl (.inr b)) =
      ((univ : Finset (Fin r)).disjSum (∅ : Finset (Fin r))).disjSum
        (univ : Finset (Fin s)) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    rcases v with (v | v) | v <;>
      simp [graph, part, Fin.ext_iff]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
  simp

theorem degree_core (r s : ℕ) (c : Fin s) :
    (graph r s).degree (.inr c) = 2 * r + s - 1 := by
  rw [← vertex_card r s]
  apply (SimpleGraph.degree_eq_card_sub_one _ _).mpr
  intro v hv
  exact ⟨hv, Or.inr rfl⟩

/-- The usual edge count without division. -/
theorem edge_card_twice (r s : ℕ) :
    2 * (graph r s).edgeFinset.card = 2 * r ^ 2 + 4 * r * s + s * (s - 1) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [Vertex, Fintype.sum_sum_type, degree_left, degree_right, degree_core,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  by_cases hs : s = 0
  · subst s
    simp
    ring
  · have hspos : 1 ≤ s := by omega
    have hsub : 2 * r + s - 1 = 2 * r + (s - 1) := by omega
    rw [hsub]
    ring

theorem edge_card_twelve (r t : ℕ) :
    (graph r (12 * t)).edgeFinset.card + 6 * t =
      r ^ 2 + 24 * r * t + 72 * t ^ 2 := by
  have h := edge_card_twice r (12 * t)
  by_cases ht : t = 0
  · subst t
    simp at h ⊢
    omega
  · have hsub : 12 * t - 1 + 1 = 12 * t := by omega
    nlinarith

/-- All non-diagonal ordered pairs carry the total available edge weight. -/
theorem total_weight (r s : ℕ) :
    ∑ e ∈ (univ : Finset (Vertex r s)).offDiag, weight e =
      12 * r * s + 2 * s * (s - 1) := by
  have hfull : (∑ v : Vertex r s, ∑ w : Vertex r s, weight (v, w)) =
      12 * r * s + 2 * s ^ 2 := by
    simp [Vertex, Fintype.sum_sum_type, weight, part, Fin.ext_iff]
    ring
  have hdiag : (∑ v : Vertex r s, weight (v, v)) = 2 * s := by
    simp [Vertex, Fintype.sum_sum_type, weight, part, Fin.ext_iff]
    omega
  have h := Finset.sum_union (f := @weight r s)
    (Finset.disjoint_diag_offDiag (univ : Finset (Vertex r s)))
  rw [Finset.diag_union_offDiag, Finset.sum_diag, Finset.sum_product] at h
  rw [hfull, hdiag] at h
  by_cases hs : s = 0
  · subst s
    simpa using h.symm
  · have hsub : s - 1 + 1 = s := by omega
    nlinarith

end TrianglePacking
