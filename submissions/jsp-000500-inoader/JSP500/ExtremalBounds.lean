import JSP500.Restriction
import JSP500.Vendor.BrouwerInduction

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The general KP saving, transported from `Fin n` to arbitrary finite vertices. -/
theorem kp_saving_finite (G : SimpleGraph V) [DecidableRel G.Adj] (r : Nat)
    (hr : 0 < r) (hn : 2*r+1 ≤ Fintype.card V)
    (hcf : G.CliqueFree (r+1)) (hnc : ¬ G.Colorable r) :
    G.edgeFinset.card + (Fintype.card V / r - 1) ≤
      SimpleGraph.turanNumber (Fintype.card V) r := by
  classical
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let iso : H ≃g G := SimpleGraph.Iso.comap e G
  have hcf' : H.CliqueFree (r+1) := hcf.comap iso.isContained
  have hnc' : ¬ H.Colorable r := fun h => hnc (h.of_hom iso.symm.toHom)
  have h := Erdos617.kp_saving hr hn H hcf' hnc'
  rw [← Erdos617.card_edgeFinset_eq_edgeCountIn H, iso.card_edgeFinset_eq] at h
  exact h

lemma colorGraph_le_other_compl (c : Sym2 V → Fin 7) {i j : Fin 7} (hij : i ≠ j) :
    colorGraph c i ≤ (colorGraph c j)ᶜ := by
  intro u v h
  exact ⟨h.1, fun h' => hij (h.2.symm.trans h'.2)⟩

/-- The strict lower edge bound for each other color, used in the core ladder.
It is written without natural subtraction. -/
theorem strict_other_color_bound (c : Sym2 V → Fin 7) (hb : Balanced c)
    {i j : Fin 7} (hij : i ≠ j) {a : Nat}
    (ha : (colorGraph c i)ᶜ.CliqueFree (a+1))
    (hcard : 7*a < Fintype.card V) (hlarge : 15 ≤ Fintype.card V) :
    (Fintype.card V).choose 2 + (Fintype.card V / 7 - 1) ≤
      (colorGraph c j).edgeFinset.card + SimpleGraph.turanNumber (Fintype.card V) 7 := by
  have hnc : ¬ (colorGraph c i).Colorable 7 := by
    intro hc
    have := card_le_of_colorable_and_independence hc ha
    omega
  have hncj : ¬ (colorGraph c j)ᶜ.Colorable 7 := by
    intro hc
    exact hnc (hc.mono_left (colorGraph_le_other_compl c hij))
  have h := kp_saving_finite (colorGraph c j)ᶜ 7 (by decide) hlarge
    (balanced_compl_cliqueFree c hb j) hncj
  have hs := edges_add_complement (colorGraph c j)
  omega

end JSP500
