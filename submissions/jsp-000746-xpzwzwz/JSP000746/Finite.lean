import JSP000746.Main

namespace JSP000746

lemma triangleFree_comap {α β : Type*} (G : SimpleGraph β) (hG : G.CliqueFree 3)
    (f : α → β) : (G.comap f).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hG {f a,f b,f c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

/-- The finite interval form, for every `n ≥ 18`, with no modular addition in the conclusion. -/
theorem erdos_895_finite_interval (n : ℕ) (hn : 18 ≤ n)
    (G : SimpleGraph (Fin (n+1))) (hG : G.CliqueFree 3) :
    ∃ a b c : Fin (n+1), 0 < a.val ∧ a.val < b.val ∧
      c.val = a.val + b.val ∧ c.val ≤ 18 ∧
      ¬G.Adj a b ∧ ¬G.Adj a c ∧ ¬G.Adj b c := by
  let f : ℕ → Fin (n+1) := fun k => ⟨k % (n+1), Nat.mod_lt _ (by omega)⟩
  obtain ⟨a,b,ha,hab,hN,h₁,h₂,h₃⟩ := independent_schur_triple_le_eighteen (G.comap f) (triangleFree_comap G hG f)
  have fa : (f a).val = a := Nat.mod_eq_of_lt (by omega)
  have fb : (f b).val = b := Nat.mod_eq_of_lt (by omega)
  have fc : (f (a+b)).val = a+b := Nat.mod_eq_of_lt (by omega)
  refine ⟨f a, f b, f (a+b), ?_, ?_, ?_, ?_, h₁,h₂,h₃⟩
  · simpa only [fa] using ha
  · simpa only [fa,fb] using hab
  · simp only [fa,fb,fc]
  · simpa only [fc] using hN

end JSP000746
