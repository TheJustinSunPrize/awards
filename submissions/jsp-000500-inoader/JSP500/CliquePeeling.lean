import JSP500.FinalFloors

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V : Type} [Fintype V] [DecidableEq V]

lemma edgeCount_clique (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V}
    (hS : G.IsClique S) : edgeCount G S = S.card.choose 2 := by
  rw [← Erdos617.card_offdiag S]
  unfold edgeCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
    exact ⟨fun h => ⟨h.1,h.2.ne⟩,fun h => ⟨h.1,hS h.1.1 h.1.2 h.2⟩⟩

lemma edgeCount_disjoint_le_total (G : SimpleGraph V) [DecidableRel G.Adj] {S T : Finset V}
    (hd : Disjoint S T) : edgeCount G S + edgeCount G T ≤ G.edgeFinset.card := by
  rw [edgeCount_eq_filter_edgeFinset,edgeCount_eq_filter_edgeFinset]
  have hdis : Disjoint (G.edgeFinset.filter (fun e => e ∈ S.sym2))
      (G.edgeFinset.filter (fun e => e ∈ T.sym2)) := by
    apply Finset.disjoint_left.mpr
    intro e hs ht
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hs' := Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp hs).2
      have ht' := Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp ht).2
      exact Finset.disjoint_left.mp hd hs'.1 ht'.1
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- Adding an outside vertex includes every edge from it into the original set. -/
lemma edgeCount_add_cross_le_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : V) (hx : x ∉ S) :
    edgeCount G S + (S.filter (fun v => G.Adj x v)).card ≤ edgeCount G (insert x S) := by
  let A := S.filter (fun v => G.Adj x v)
  let spokes := A.image (fun v => s(x,v))
  have hinj : Set.InjOn (fun v => s(x,v)) A := by
    intro u hu v hv huv
    rcases Sym2.eq_iff.mp huv with h | h
    · exact h.2
    · exact False.elim (hx (h.2 ▸ (Finset.mem_filter.mp hu).1))
  have hc : spokes.card = A.card := Finset.card_image_of_injOn hinj
  have hdis : Disjoint (S.sym2.filter (fun e => e ∈ G.edgeSet)) spokes := by
    apply Finset.disjoint_left.mpr
    intro e he hs
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hs
    exact hx (Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp he).1).1
  have hsub : (S.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes ⊆
      (insert x S).sym2.filter (fun e => e ∈ G.edgeSet) := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_filter.mpr ⟨Finset.sym2_mono (Finset.subset_insert x S)
        (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hvS,hxv⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr
        ⟨Finset.mem_insert_self x S,Finset.mem_insert_of_mem hvS⟩,hxv⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hc] at h
  exact h

lemma outside_clique_neighbor_bound (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (B : Finset V) (hB : (colorGraph c k).IsNClique 7 B) (x : V) (hx : x ∉ B) :
    (B.filter (fun v => (colorGraph c k).Adj x v)).card ≤ 1 := by
  have hi := edgeCount_add_cross_le_insert (colorGraph c k) B x hx
  have hcap := local_cap_twenty_two c hb (insert x B)
    (by rw [Finset.card_insert_of_notMem hx,hB.card_eq]) k
  rw [← edgeCount_color] at hcap
  rw [edgeCount_clique _ hB.isClique,hB.card_eq] at hi
  norm_num only [Nat.choose_two_right] at hi
  omega

/-- At most six outside vertices cannot forbid every vertex of a seven-clique. -/
lemma exists_clique_representative (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (B : Finset V) (hB : (colorGraph c k).IsNClique 7 B)
    (A : Finset V) (hd : Disjoint A B) (hA : A.card ≤ 6) :
    ∃ v ∈ B, ∀ u ∈ A, ¬ (colorGraph c k).Adj u v := by
  let bad := A.biUnion (fun u => B.filter (fun v => (colorGraph c k).Adj u v))
  have hbound : bad.card ≤ A.card := by
    calc
      _ ≤ ∑ u ∈ A, (B.filter (fun v => (colorGraph c k).Adj u v)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ A, 1 := Finset.sum_le_sum (fun u hu =>
        outside_clique_neighbor_bound c hb k B hB u (fun huB => Finset.disjoint_left.mp hd hu huB))
      _ = _ := by simp
  have hnot : ¬ B ⊆ bad := by
    intro hs
    have h := Finset.card_le_card hs
    rw [hB.card_eq] at h
    omega
  obtain ⟨v,hvB,hvbad⟩ := Finset.not_subset.mp hnot
  refine ⟨v,hvB,?_⟩
  intro u hu hadj
  exact hvbad (Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨hvB,hadj⟩⟩)

/-- Deleting one seven-clique decreases the independence cap by one. -/
theorem clique_deletion_alpha (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    {a : Nat} (ha6 : a ≤ 6) (ha : (colorGraph c k)ᶜ.CliqueFree (a+1))
    (B : Finset V) (hB : (colorGraph c k).IsNClique 7 B) :
    (colorGraph (restrictColor c (Finset.univ \ B)) k)ᶜ.CliqueFree a := by
  rw [compl_colorGraph_restrict]
  intro Q hQ
  let A := Q.image Subtype.val
  have hA : A.card = a := by rw [Finset.card_image_of_injective _ Subtype.val_injective,hQ.card_eq]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    obtain ⟨v',_,rfl⟩ := Finset.mem_image.mp hvA
    exact (Finset.mem_sdiff.mp v'.property).2 hvB
  have hcl : (colorGraph c k)ᶜ.IsNClique a A := by
    refine ⟨?_,hA⟩
    intro u hu v hv huv
    obtain ⟨u',huQ,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v',hvQ,rfl⟩ := Finset.mem_image.mp hv
    exact hQ.isClique huQ hvQ (fun h => huv (congrArg Subtype.val h))
  obtain ⟨v,hvB,hv⟩ := exists_clique_representative c hb k B hB A hdis (by omega)
  apply ha _ (hcl.insert (a := v) ?_)
  intro u hu
  refine ⟨fun h => Finset.disjoint_left.mp hdis hu (h ▸ hvB),?_⟩
  exact fun h => hv u hu h.symm

end JSP500
