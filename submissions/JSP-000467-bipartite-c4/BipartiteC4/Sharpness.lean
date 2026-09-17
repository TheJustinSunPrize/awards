import BipartiteC4.Construction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace BipartiteC4

open Finset

theorem vertex_card (a b : ℕ) : Fintype.card (Vertex a b) = a+b := by
  simp [Vertex]

theorem degree_left (a b : ℕ) (x : Fin a) :
    (graph a b).degree (Sum.inl x) = b := by
  have hn : (graph a b).neighborFinset (Sum.inl x) =
      (univ : Finset (Fin b)).image (Sum.inr : Fin b → Vertex a b) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v <;> simp [graph, completeBipartiteGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inr_injective]
  simp

theorem degree_right (a b : ℕ) (y : Fin b) :
    (graph a b).degree (Sum.inr y) = a := by
  have hn : (graph a b).neighborFinset (Sum.inr y) =
      (univ : Finset (Fin a)).image (Sum.inl : Fin a → Vertex a b) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v <;> simp [graph, completeBipartiteGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inl_injective]
  simp

theorem min_degree (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    (graph a b).minDegree = min a b := by
  let : Nonempty (Vertex a b) := ⟨Sum.inl ⟨0,ha⟩⟩
  apply le_antisymm
  · have hl := (graph a b).minDegree_le_degree (Sum.inl ⟨0,ha⟩)
    have hr := (graph a b).minDegree_le_degree (Sum.inr ⟨0,hb⟩)
    rw [degree_left] at hl
    rw [degree_right] at hr
    exact le_min hr hl
  · apply (graph a b).le_minDegree_of_forall_le_degree
    intro v
    cases v with
    | inl x => rw [degree_left]; exact min_le_right a b
    | inr y => rw [degree_right]; exact min_le_left a b

theorem edge_card (a b : ℕ) : (graph a b).edgeFinset.card = a*b := by
  have h := (graph a b).sum_degrees_eq_twice_card_edges
  simp only [Vertex, Fintype.sum_sum_type, degree_left, degree_right,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  nlinarith

/-- Exact packing capacity of the sharpness family for Wang's theorem. -/
theorem sharp_capacity (k q : ℕ) (hk : 0<k) :
    HasPacking (graph (2*k-1) (2*k+1)) q ↔ q ≤ k-1 := by
  rw [exact_capacity]
  omega

/-- For every positive k, degree 2k-1 on 4k vertices does not force a C4 factor. -/
theorem sharpness (k : ℕ) (hk : 0<k) :
    Fintype.card (Vertex (2*k-1) (2*k+1)) = 4*k ∧
    (graph (2*k-1) (2*k+1)).minDegree = 2*k-1 ∧
    HasPacking (graph (2*k-1) (2*k+1)) (k-1) ∧
    ¬HasPacking (graph (2*k-1) (2*k+1)) k := by
  refine ⟨?_, ?_, (sharp_capacity k (k-1) hk).mpr le_rfl, ?_⟩
  · rw [vertex_card]
    omega
  · rw [min_degree _ _ (by omega) (by omega)]
    omega
  · rw [sharp_capacity k k hk]
    omega

/-- Any universal minimum-degree threshold for C4 factors is at least 2k. -/
theorem necessary_degree_threshold (k d : ℕ) (hk : 0<k)
    (h : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 4*k → d ≤ G.minDegree → HasPacking G k) : 2*k ≤ d := by
  obtain ⟨hn,hd,_,hnot⟩ := sharpness k hk
  by_contra hsmall
  exact hnot (h _ _ hn (by omega))

/-- Sharpness obstructions exist above every prescribed graph order. -/
theorem arbitrarily_large_sharpness (N : ℕ) :
    ∃ k : ℕ, 0<k ∧ N ≤ Fintype.card (Vertex (2*k-1) (2*k+1)) ∧
      (graph (2*k-1) (2*k+1)).minDegree = 2*k-1 ∧
      ¬HasPacking (graph (2*k-1) (2*k+1)) k := by
  have hk : 0<N+1 := by omega
  obtain ⟨hn,hd,_,hnot⟩ := sharpness (N+1) hk
  exact ⟨N+1,hk,by omega,hd,hnot⟩

end BipartiteC4
