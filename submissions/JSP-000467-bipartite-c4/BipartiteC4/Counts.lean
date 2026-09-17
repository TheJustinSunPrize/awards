import BipartiteC4.Basic

namespace BipartiteC4

open Finset

/-- Every C4 in a bipartite graph uses two vertices of each class. -/
theorem cycle_left_count {a b : ℕ} (v : Fin 4 → Vertex a b)
    (h : ∀ j, (graph a b).Adj (v j) (v (j+1))) :
    ((univ : Finset (Fin 4)).filter fun j => (v j).isLeft).card = 2 := by
  classical
  have h01 := h 0
  have h12 := h 1
  have h23 := h 2
  norm_num at h01 h12 h23
  rw [card_eq_sum_ones, sum_filter]
  simp only [Fin.sum_univ_four]
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp_all [graph, completeBipartiteGraph]

/-- Arbitrary packings, with arbitrary orientations, use `2*k` left vertices. -/
theorem Packing.left_positions_card {a b k : ℕ} (p : Packing (graph a b) k) :
    ((univ : Finset (Fin k × Fin 4)).filter fun x => (p.vertices x).isLeft).card =
      2*k := by
  classical
  have hlocal (i : Fin k) :
      (∑ j : Fin 4, if (p.vertices (i,j)).isLeft then 1 else 0) = 2 := by
    simpa only [card_eq_sum_ones, sum_filter] using
      cycle_left_count (fun j => p.vertices (i,j)) (p.adjacent i)
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  simp_rw [hlocal]
  simp [Nat.mul_comm]

theorem Packing.left_bound {a b k : ℕ} (p : Packing (graph a b) k) : 2*k ≤ a := by
  classical
  let L := (univ : Finset (Fin k × Fin 4)).filter fun x => (p.vertices x).isLeft
  have hsub : L.image p.vertices ⊆
      (univ : Finset (Fin a)).image (Sum.inl : Fin a → Vertex a b) := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    have hxleft := (mem_filter.mp hx).2
    cases he : p.vertices x with
    | inl y => exact mem_image.mpr ⟨y, mem_univ _, rfl⟩
    | inr y => simp [he] at hxleft
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ p.vertices.injective,
    card_image_of_injective _ Sum.inl_injective, card_univ, Fintype.card_fin] at hcard
  exact (p.left_positions_card ▸ hcard)

theorem Packing.right_bound {a b k : ℕ} (p : Packing (graph a b) k) : 2*k ≤ b :=
  p.swap.left_bound

/-- A uniform upper bound, applying to every genuine C4 packing. -/
theorem packing_upper_bound {a b k : ℕ} (h : HasPacking (graph a b) k) :
    k ≤ min (a/2) (b/2) := by
  obtain ⟨p⟩ := h
  have hl := p.left_bound
  have hr := p.right_bound
  omega

end BipartiteC4
