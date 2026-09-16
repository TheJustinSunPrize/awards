import Statement

set_option autoImplicit false

namespace JSP001021

 theorem tournament_transitive_subtournament
    (k : Nat) :
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α), Fintype.card α = 2 ^ k →
      ∃ f : Fin (k + 1) → α, TransitiveEmbedding T (k + 1) f := by
  induction k with
  | zero =>
      intro α _ _ T hcard
      have hpos : 0 < Fintype.card α := by simp [hcard]
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      let f : Fin 1 → α := fun _ => v
      refine ⟨f, ?_⟩
      constructor
      · intro i j _
        exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
      · intro i j hij
        omega
  | succ k ih =>
      intro α _ _ T hcard
      have hpos : 0 < Fintype.card α := by
        rw [hcard]
        positivity
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      let rest : Finset α := Finset.univ.erase v
      let out : Finset α := rest.filter (fun x => T.edge v x)
      let inn : Finset α := rest.filter (fun x => T.edge x v)
      have hout_union : out ∪ inn = rest := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_filter.mp hx).1
        · intro hx
          have hvx_ne : v ≠ x := by
            intro hvx
            subst hvx
            exact (Finset.mem_erase.mp hx).1 rfl
          by_cases hvx : T.edge v x
          · exact Finset.mem_union_left inn (Finset.mem_filter.mpr ⟨hx, hvx⟩)
          · have hxv : T.edge x v := by
              rcases T.complete (a := v) (b := x) hvx_ne with h | h
              · exact False.elim (hvx h)
              · exact h
            exact Finset.mem_union_right out (Finset.mem_filter.mpr ⟨hx, hxv⟩)
      have hout_disjoint : Disjoint out inn := by
        rw [Finset.disjoint_left]
        intro x hxout hxinn
        have hvx : T.edge v x := (Finset.mem_filter.mp hxout).2
        have hxv : T.edge x v := (Finset.mem_filter.mp hxinn).2
        exact T.antisymm hvx hxv
      have hsum : out.card + inn.card = 2 ^ (k + 1) - 1 := by
        have hcard_rest : rest.card = 2 ^ (k + 1) - 1 := by
          rw [show rest = Finset.univ.erase v from rfl]
          rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
        calc
          out.card + inn.card = (out ∪ inn).card :=
            (Finset.card_union_of_disjoint hout_disjoint).symm
          _ = rest.card := by rw [hout_union]
          _ = 2 ^ (k + 1) - 1 := hcard_rest
      have hlarge : 2 ^ k ≤ out.card ∨ 2 ^ k ≤ inn.card := by
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
        rw [hpow] at hsum
        omega
      rcases hlarge with hout | hinn
      · obtain ⟨s, hsout, hscard⟩ := Finset.exists_subset_card_eq hout
        let β := {x // x ∈ s}
        let U : Tournament β :=
          { edge := fun a b => T.edge a.1 b.1
            complete := by
              intro a b hab
              rcases T.complete (a := a.1) (b := b.1) (by
                intro heq
                apply hab
                exact Subtype.ext heq) with h | h
              · exact Or.inl h
              · exact Or.inr h
            antisymm := by
              intro a b hab hba
              exact T.antisymm hab hba
            edge_decidable := fun a b => inferInstance }
        have hβcard : Fintype.card β = 2 ^ k := by
          rw [Fintype.card_coe]
          exact hscard
        obtain ⟨g, hg⟩ := ih U hβcard
        have hgv_ne : ∀ i : Fin (k + 1), (g i).1 ≠ v := by
          intro i heq
          have hiout : (g i).1 ∈ out := hsout (g i).property
          have hirest : (g i).1 ∈ rest := (Finset.mem_filter.mp hiout).1
          exact (Finset.mem_erase.mp hirest).1 heq
        have hgv_out : ∀ i : Fin (k + 1), T.edge v (g i).1 := by
          intro i
          exact (Finset.mem_filter.mp (hsout (g i).property)).2
        let f : Fin (k + 2) → α :=
          Fin.cases v (fun i => (g i).1)
        refine ⟨f, ?_⟩
        constructor
        · intro i j hij
          revert j
          cases i using Fin.cases with
          | zero =>
            intro j h
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
              exfalso
              apply hgv_ne j
              simpa [f] using h.symm
          | succ i =>
            intro j h
            cases j using Fin.cases with
            | zero =>
              exfalso
              apply hgv_ne i
              simpa [f] using h
            | succ j =>
              have hgg : g i = g j := by
                apply Subtype.ext
                simpa [f] using h
              have hij' : i = j := hg.1 hgg
              simpa [hij']
        · intro i j hij
          revert j
          cases i using Fin.cases with
          | zero =>
            intro j hij
            cases j using Fin.cases with
            | zero => omega
            | succ j => simpa [f] using hgv_out j
          | succ i =>
            intro j hij
            cases j using Fin.cases with
            | zero => exact False.elim (Fin.not_lt_zero _ hij)
            | succ j =>
              have hij' : i < j := (Fin.succ_lt_succ_iff).mp hij
              simpa [f, U] using hg.2 hij'
      · obtain ⟨s, hsinn, hscard⟩ := Finset.exists_subset_card_eq hinn
        let β := {x // x ∈ s}
        let U : Tournament β :=
          { edge := fun a b => T.edge a.1 b.1
            complete := by
              intro a b hab
              rcases T.complete (a := a.1) (b := b.1) (by
                intro heq
                apply hab
                exact Subtype.ext heq) with h | h
              · exact Or.inl h
              · exact Or.inr h
            antisymm := by
              intro a b hab hba
              exact T.antisymm hab hba
            edge_decidable := fun a b => inferInstance }
        have hβcard : Fintype.card β = 2 ^ k := by
          rw [Fintype.card_coe]
          exact hscard
        obtain ⟨g, hg⟩ := ih U hβcard
        have hgv_ne : ∀ i : Fin (k + 1), (g i).1 ≠ v := by
          intro i heq
          have hiinn : (g i).1 ∈ inn := hsinn (g i).property
          have hirest : (g i).1 ∈ rest := (Finset.mem_filter.mp hiinn).1
          exact (Finset.mem_erase.mp hirest).1 heq
        have hgv_inn : ∀ i : Fin (k + 1), T.edge (g i).1 v := by
          intro i
          exact (Finset.mem_filter.mp (hsinn (g i).property)).2
        let f : Fin (k + 2) → α :=
          Fin.lastCases v (fun i => (g i).1)
        refine ⟨f, ?_⟩
        constructor
        · intro i j hij
          revert j
          cases i using Fin.lastCases with
          | last =>
            intro j h
            cases j using Fin.lastCases with
            | last => rfl
            | cast j =>
              exfalso
              apply hgv_ne j
              simpa [f] using h.symm
          | cast i =>
            intro j h
            cases j using Fin.lastCases with
            | last =>
              exfalso
              apply hgv_ne i
              simpa [f] using h
            | cast j =>
              have hgg : g i = g j := by
                apply Subtype.ext
                simpa [f] using h
              have hij' : i = j := hg.1 hgg
              simpa [hij']
        · intro i j hij
          revert j
          cases i using Fin.lastCases with
          | last =>
            intro j hij
            cases j using Fin.lastCases with
            | last => exact False.elim (lt_irrefl _ hij)
            | cast j => exact False.elim ((not_lt_of_ge (Fin.le_last j.castSucc)) hij)
          | cast i =>
            intro j hij
            cases j using Fin.lastCases with
            | last => simpa [f] using hgv_inn i
            | cast j =>
              have hij' : i < j := (Fin.castSucc_lt_castSucc_iff).mp hij
              simpa [f, U] using hg.2 hij'


theorem solution : JSP001021Statement := by
  intro k α _ _ T hcard
  exact tournament_transitive_subtournament k T hcard

end JSP001021
