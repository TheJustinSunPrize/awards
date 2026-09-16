import Mathlib

/-!
Finite hypergraphs and proper vertex colourings for JSP-000692 / Erdős 836.
There are no assumptions about the desired intersection bound in these definitions.
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

/-- Exactly three-chromatic: a proper 3-colouring exists and no proper
2-colouring exists. Bool has exactly two colours. -/
def ThreeChromatic (H : Hypergraph V) : Prop :=
  (∃ c : V → Fin 3, Proper H c) ∧ ¬ (∃ c : V → Bool, Proper H c)

/-- Every transversal contains an edge in a non-two-colourable hypergraph. -/
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

end JSP692
