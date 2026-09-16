import JSP500.ColoredTerminal

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]

def restrictColor (c : Sym2 V → Fin 7) (S : Finset V) : Sym2 ↥S → Fin 7 :=
  fun e => c (Sym2.map Subtype.val e)

lemma balanced_restrict (c : Sym2 V → Fin 7) (hb : Balanced c) (S : Finset V) :
    Balanced (restrictColor c S) := by
  classical
  intro T hT k hm
  apply hb (T.image Subtype.val)
    (by rw [Finset.card_image_of_injective _ Subtype.val_injective, hT]) k
  intro u hu v hv huv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hv
  exact hm a ha b hb' (fun h => huv (congrArg Subtype.val h))

lemma colorGraph_restrict (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) :
    colorGraph (restrictColor c S) k = (colorGraph c k).comap Subtype.val := by
  ext a b
  simp [colorGraph, restrictColor, Subtype.val_inj]

lemma compl_colorGraph_restrict (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) :
    (colorGraph (restrictColor c S) k)ᶜ = (colorGraph c k)ᶜ.comap Subtype.val := by
  ext a b
  simp [colorGraph, restrictColor, Subtype.val_inj]

/-- The colored terminal core at any order at least fourteen. -/
theorem no_colored_terminal (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : 14 ≤ Fintype.card V) (k : Fin 7)
    (halpha : (colorGraph c k)ᶜ.CliqueFree 3)
    (homega : (colorGraph c k).CliqueFree 7) : False := by
  classical
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (show 14 ≤ (Finset.univ : Finset V).card by simpa using hn)
  apply no_colored_terminal_fourteen (restrictColor c S) (balanced_restrict c hb S)
    (by simpa using hS) k
  · rw [compl_colorGraph_restrict]
    exact Erdos617.R6.Brooks.cliqueFree_comap (colorGraph c k)ᶜ S halpha
  · rw [colorGraph_restrict]
    exact Erdos617.R6.Brooks.cliqueFree_comap (colorGraph c k) S homega

end JSP500
