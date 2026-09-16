import JSP500.DirectFloors
import JSP500.SevenVertex

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pair_extension_core (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7)
    (u v : V) (huv : (colorGraph c k)ᶜ.Adj u v) (T : Finset V)
    (hT : ∀ w ∈ T, (colorGraph c k)ᶜ.Adj u w ∧ (colorGraph c k)ᶜ.Adj v w) : T.card < 14 := by
  by_contra hcard
  apply no_colored_terminal (restrictColor c T) (balanced_restrict c hb T)
    (by simpa using (show 14 ≤ T.card by omega)) k
  · rw [compl_colorGraph_restrict]
    intro Q hQ
    have hcl : (colorGraph c k)ᶜ.IsNClique 3 (Q.image Subtype.val) := by
      refine ⟨?_,by rw [Finset.card_image_of_injective _ Subtype.val_injective, hQ.card_eq]⟩
      intro a ha' b hb' hab
      obtain ⟨a',haQ,rfl⟩ := Finset.mem_image.mp ha'
      obtain ⟨b',hbQ,rfl⟩ := Finset.mem_image.mp hb'
      exact hQ.isClique haQ hbQ (fun he => hab (congrArg Subtype.val he))
    have hnear : ∀ w ∈ Q.image Subtype.val,
        (colorGraph c k)ᶜ.Adj u w ∧ (colorGraph c k)ᶜ.Adj v w := by
      intro w hw
      obtain ⟨w',_,rfl⟩ := Finset.mem_image.mp hw
      exact hT w' w'.property
    have hc4 := hcl.insert (a := v) (fun w hw => (hnear w hw).2)
    apply ha _ (hc4.insert (a := u) ?_)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact huv
    · exact (hnear w hw).1
  · rw [colorGraph_restrict]
    exact Erdos617.R6.Brooks.cliqueFree_comap _ _ ho

/-- For a nonadjacent pair outside W, the union of their neighbors in W
must cover all but thirteen vertices of W. -/
theorem pair_cover_size (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7)
    (u v : V) (huv : (colorGraph c k)ᶜ.Adj u v) (W : Finset V)
    (hu : u ∉ W) (hv : v ∉ W) :
    W.card ≤ 13 + ((W.filter (fun w => (colorGraph c k).Adj u w)) ∪
      (W.filter (fun w => (colorGraph c k).Adj v w))).card := by
  let C := (W.filter (fun w => (colorGraph c k).Adj u w)) ∪
    (W.filter (fun w => (colorGraph c k).Adj v w))
  have hclt : (W \ C).card < 14 := by
    apply pair_extension_core c hb k ha ho u v huv
    intro w hw
    obtain ⟨hwW,hwC⟩ := Finset.mem_sdiff.mp hw
    have huw : u ≠ w := fun h => hu (h ▸ hwW)
    have hvw : v ≠ w := fun h => hv (h ▸ hwW)
    refine ⟨⟨huw,?_⟩,⟨hvw,?_⟩⟩
    · intro hadj
      exact hwC (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwW,hadj⟩))
    · intro hadj
      exact hwC (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwW,hadj⟩))
  have hsub : C ⊆ W := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have he := Finset.card_sdiff_add_card_eq_card hsub
  change W.card ≤ 13+C.card
  omega

lemma pair_cross_degree_lower (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7)
    (u v : V) (huv : (colorGraph c k)ᶜ.Adj u v) (W : Finset V)
    (hu : u ∉ W) (hv : v ∉ W) :
    W.card ≤ 13 + (W.filter (fun w => (colorGraph c k).Adj u w)).card +
      (W.filter (fun w => (colorGraph c k).Adj v w)).card := by
  have h := pair_cover_size c hb k ha ho u v huv W hu hv
  have hc := Finset.card_union_le (W.filter (fun w => (colorGraph c k).Adj u w))
    (W.filter (fun w => (colorGraph c k).Adj v w))
  omega

end JSP500
