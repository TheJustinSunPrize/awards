import Mathlib

set_option autoImplicit false

/-!
JSP-000692 / Erdős 836: definitions and elementary structural lemmas.
Authoring status: NOT COMPILED in this environment.
Shared definitions; all counts below refer to active vertices.
-/

namespace JSP692

abbrev Hypergraph (V : Type*) := Finset (Finset V)

variable {V : Type*} [DecidableEq V]

def Uniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def Intersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty

def Proper {C : Type*} (H : Hypergraph V) (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def Mono {C : Type*} (e : Finset V) (c : V → C) : Prop :=
  ∃ b : C, ∀ x ∈ e, c x = b

def ThreeChromatic (H : Hypergraph V) : Prop :=
  (∃ c : V → Fin 3, Proper H c) ∧ ¬ (∃ c : V → Bool, Proper H c)

/-- The union of the edges, not the ambient vertex type. -/
def support (H : Hypergraph V) : Finset V := H.biUnion id

theorem not_proper_of_mono {C : Type*} {H : Hypergraph V} {c : V → C}
    {e : Finset V} (he : e ∈ H) (hm : Mono e c) : ¬ Proper H c := by
  rintro hp
  obtain ⟨b, hb⟩ := hm
  obtain ⟨u, hu, v, hv, huv⟩ := hp e he
  exact huv ((hb u hu).trans (hb v hv).symm)

/-- Every transversal contains an edge in a non-two-colorable hypergraph. -/
theorem transversal_contains_edge {H : Hypergraph V}
    (hn : ¬ ∃ c : V → Bool, Proper H c)
    (S : Finset V) (hit : ∀ e ∈ H, (e ∩ S).Nonempty) :
    ∃ e ∈ H, e ⊆ S := by
  classical
  by_contra h
  apply hn
  refine ⟨fun x => decide (x ∈ S), ?_⟩
  intro e he
  obtain ⟨u, hu⟩ := hit e he
  have hue := (Finset.mem_inter.mp hu).1
  have huS := (Finset.mem_inter.mp hu).2
  have hout : ∃ v ∈ e, v ∉ S := by
    by_contra hv
    apply h
    refine ⟨e, he, ?_⟩
    intro v hve
    by_contra hvS
    exact hv ⟨v, hve, hvS⟩
  obtain ⟨v, hve, hvS⟩ := hout
  refine ⟨u, hue, v, hve, ?_⟩
  simp [huS, hvS]

/-- Intersecting uniform hypergraphs of rank at least two are 3-colorable. -/
theorem threeColorable_of_intersecting {H : Hypergraph V} {r : ℕ}
    (hr : 2 ≤ r) (hu : Uniform H r) (hi : Intersecting H) :
    ∃ c : V → Fin 3, Proper H c := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨e, he⟩ := hH
    have hepos : 0 < e.card := by rw [hu e he]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hepos
    have hrest : (e.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx, hu e he]
      omega
    let c : V → Fin 3 := fun v => if v = x then 0 else if v ∈ e then 1 else 2
    refine ⟨c, ?_⟩
    intro f hf
    by_cases hfe : f = e
    · subst f
      obtain ⟨y, hy⟩ := hrest
      have hyx := (Finset.mem_erase.mp hy).1
      have hye := (Finset.mem_erase.mp hy).2
      refine ⟨x, hx, y, hye, ?_⟩
      simp [c, hyx, hye]
    · have hout : ∃ w ∈ f, w ∉ e := by
        by_contra h
        have hsub : f ⊆ e := by
          intro w hw
          by_contra hwe
          exact h ⟨w, hw, hwe⟩
        apply hfe
        apply Finset.eq_of_subset_of_card_le hsub
        rw [hu e he, hu f hf]
      obtain ⟨w, hwf, hwe⟩ := hout
      obtain ⟨v, hv⟩ := hi f hf e he
      have hvf := (Finset.mem_inter.mp hv).1
      have hve := (Finset.mem_inter.mp hv).2
      have hwx : w ≠ x := by
        intro hwx
        exact hwe (hwx.symm ▸ hx)
      refine ⟨v, hvf, w, hwf, ?_⟩
      by_cases hvx : v = x
      · simp [c, hvx, hwx, hwe]
      · simp [c, hvx, hve, hwx, hwe]
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    refine ⟨fun _ => 0, ?_⟩
    simp [Proper, hEmpty]

end JSP692
