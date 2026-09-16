/- Generic finite-vertex versions of counting/transport lemmas adapted from
nwinter/erdos-617-r5, pinned source and Apache-2.0 license in THIRD_PARTY_NOTICES.md. -/
import JSP500.CoreLadder

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Nat :=
  (S.sym2.filter (fun e => e ∈ G.edgeSet)).card

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edgeCount_mono {S S' : Finset (V)} (h : S ⊆ S') :
    edgeCount G S ≤ edgeCount G S' := by
  unfold edgeCount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.sym2_mono h

/-- Trivial upper bound: at most `C(|S|, 2)` edges inside `S`. -/
theorem edgeCount_le_choose_two (S : Finset (V)) :
    edgeCount G S ≤ S.card.choose 2 := by
  rw [← Erdos617.card_offdiag S]
  unfold edgeCount
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  refine ⟨he.1, ?_⟩
  exact G.not_isDiag_of_mem_edgeSet he.2

/-- `edgeCount` counted from the edge side: the `G`-edges lying inside `S`. -/
theorem edgeCount_eq_filter_edgeFinset (S : Finset (V)) :
    edgeCount G S = (G.edgeFinset.filter (fun e => e ∈ S.sym2)).card := by
  unfold edgeCount
  apply Finset.card_bij (fun e _ => e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨G.mem_edgeFinset.mpr he.2, he.1⟩
  · intro a _ b _ hab; exact hab
  · intro e he
    rw [Finset.mem_filter] at he
    exact ⟨e, by rw [Finset.mem_filter]; exact ⟨he.2, G.mem_edgeFinset.mp he.1⟩, rfl⟩

/-- Total edge count via `edgeFinset`. -/
theorem edgeCount_univ_eq_card_edgeFinset :
    edgeCount G Finset.univ = G.edgeFinset.card := by
  unfold edgeCount
  rw [Finset.sym2_univ]
  congr 1
  ext e
  simp [G.mem_edgeFinset]


theorem edgeCount_add_card_le_insert {v : V} {A : Finset (V)}
    (hA : A ⊆ G.neighborFinset v) (hvA : v ∉ A) :
    edgeCount G A + A.card ≤ edgeCount G (insert v A) := by
  set spokes := A.image (fun w => s(v, w)) with hsp
  have hinj : Set.InjOn (fun w => s(v, w)) A := by
    intro a ha b hb hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨_, hav⟩
    · exact h
    · exact absurd (hav ▸ (Finset.mem_coe.mp ha)) hvA
  have hspoke_card : spokes.card = A.card := by
    rw [hsp, Finset.card_image_of_injOn hinj]
  have hsub : (A.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes
      ⊆ (insert v A).sym2.filter (fun e => e ∈ G.edgeSet) := by
    intro e he
    rw [Finset.mem_union] at he
    rw [Finset.mem_filter]
    rcases he with he | he
    · rw [Finset.mem_filter] at he
      exact ⟨Finset.sym2_mono (Finset.subset_insert v A) he.1, he.2⟩
    · rw [hsp, Finset.mem_image] at he
      obtain ⟨w, hw, rfl⟩ := he
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_insert_self v A, Finset.mem_insert_of_mem hw⟩
      · rw [SimpleGraph.mem_edgeSet]
        exact (G.mem_neighborFinset v w).mp (hA hw)
  have hdisj : Disjoint (A.sym2.filter (fun e => e ∈ G.edgeSet)) spokes := by
    rw [Finset.disjoint_left]
    intro e he hesp
    rw [Finset.mem_filter] at he
    rw [hsp, Finset.mem_image] at hesp
    obtain ⟨w, hw, hwe⟩ := hesp
    have := he.1
    rw [← hwe, Finset.mk_mem_sym2_iff] at this
    exact hvA this.1
  calc edgeCount G A + A.card
      = (A.sym2.filter (fun e => e ∈ G.edgeSet)).card + spokes.card := by
        unfold edgeCount; rw [hspoke_card]
    _ = ((A.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ ((insert v A).sym2.filter (fun e => e ∈ G.edgeSet)).card := Finset.card_le_card hsub
    _ = edgeCount G (insert v A) := rfl


theorem edgeCount_comap (X : SimpleGraph (V)) [DecidableRel X.Adj] (f : W ↪ V)
    (T : Finset (W)) :
    edgeCount (X.comap f) T = edgeCount X (T.image f) := by
  unfold edgeCount
  apply Finset.card_bij (fun e _ => Sym2.map f e)
  · -- maps to
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, hedge⟩ := he
      rw [Finset.mk_mem_sym2_iff] at hmem
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj] at hedge
      rw [Finset.mem_filter, Sym2.map_mk]
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_image_of_mem f hmem.1, Finset.mem_image_of_mem f hmem.2⟩
      · rw [SimpleGraph.mem_edgeSet]; exact hedge
  · -- injective
    intro a _ b _ hab
    exact Sym2.map.injective f.injective hab
  · -- surjective
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, hedge⟩ := he
      rw [Finset.mk_mem_sym2_iff] at hmem
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hmem.1
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hmem.2
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj]
        rw [SimpleGraph.mem_edgeSet] at hedge
        exact hedge
      · rw [Sym2.map_mk]


theorem adj_of_edgeCount_choose (X : SimpleGraph (V)) [DecidableRel X.Adj] (S : Finset (V))
    (h : S.card.choose 2 ≤ edgeCount X S) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) : X.Adj u v := by
  have hsub : S.sym2.filter (fun e => e ∈ X.edgeSet) ⊆ S.sym2.filter (fun e => ¬ e.IsDiag) := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, X.not_isDiag_of_mem_edgeSet he.2⟩
  have hcard : (S.sym2.filter (fun e => ¬ e.IsDiag)).card ≤ (S.sym2.filter (fun e => e ∈ X.edgeSet)).card := by
    rw [Erdos617.card_offdiag]; exact h
  have heq : S.sym2.filter (fun e => e ∈ X.edgeSet) = S.sym2.filter (fun e => ¬ e.IsDiag) :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : s(u, v) ∈ S.sym2.filter (fun e => ¬ e.IsDiag) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩, by rw [Sym2.mk_isDiag_iff]; exact huv⟩
  rw [← heq, Finset.mem_filter, SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2


/-- Edge counts on an induced vertex set agree with the ambient count. -/
lemma edgeCount_induced (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.comap (Subtype.val : ↥S → V)).edgeFinset.card = edgeCount G S := by
  calc
    _ = edgeCount (G.comap (Subtype.val : ↥S → V)) Finset.univ :=
      (edgeCount_univ_eq_card_edgeFinset _).symm
    _ = edgeCount G S := by
      have h := edgeCount_comap G (⟨Subtype.val, Subtype.val_injective⟩ : ↥S ↪ V) Finset.univ
      simpa using h

lemma edgeCount_color (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) :
    edgeCount (colorGraph c k) S = (edgesOn c S k).card := by
  classical
  unfold edgeCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp +instances only [Finset.mem_filter, Finset.mk_mem_sym2_iff,
      SimpleGraph.mem_edgeSet, edgesOn, mk_mem_pairsOn]
    change ((u ∈ S ∧ v ∈ S) ∧ (u ≠ v ∧ c s(u,v) = k)) ↔ _
    simp only [and_assoc]

/-- A degree sum over a vertex set, counted from the edge side. -/
lemma sum_degrees_in_set (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ v ∈ S, G.degree v) = ∑ e ∈ G.edgeFinset, (S.filter (fun v => v ∈ e)).card := by
  have hi : ∀ v, G.degree v = (G.edgeFinset.filter (fun e => v ∈ e)).card := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
  simp_rw [hi, Finset.card_filter]
  exact Finset.sum_comm

/-- Exact accounting around one vertex: edges among its nonneighbors plus
the degree sum of its neighbors equal all edges plus edges inside its neighborhood. -/
theorem neighborhood_accounting (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    edgeCount G (Gᶜ.neighborFinset x) + (∑ v ∈ G.neighborFinset x, G.degree v) =
      G.edgeFinset.card + edgeCount G (G.neighborFinset x) := by
  rw [sum_degrees_in_set, edgeCount_eq_filter_edgeFinset, edgeCount_eq_filter_edgeFinset]
  simp only [Finset.card_filter]
  have hc : G.edgeFinset.card = ∑ _e ∈ G.edgeFinset, 1 := by simp
  rw [hc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  revert he
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro he
    have hadj : G.Adj u v := by simpa using he
    have hpair : (G.neighborFinset x).filter (fun w => w ∈ (s(u,v) : Sym2 V)) =
        ({u,v} : Finset V).filter (fun w => w ∈ G.neighborFinset x) := by
      ext w
      simp [Sym2.mem_iff, and_comm]
    have hcnt : (∑ w ∈ G.neighborFinset x, if w ∈ (s(u,v) : Sym2 V) then 1 else 0) =
        (if u ∈ G.neighborFinset x then 1 else 0) +
        (if v ∈ G.neighborFinset x then 1 else 0) := by
      rw [← Finset.card_filter, hpair, Finset.card_filter, Finset.sum_pair hadj.ne]
    rw [hcnt]
    have hadj' := hadj.symm
    by_cases hxu : x = u <;> by_cases hxv : x = v <;>
      by_cases hu : G.Adj x u <;> by_cases hv : G.Adj x v
    all_goals simp_all [Finset.mk_mem_sym2_iff, SimpleGraph.mem_neighborFinset,
      SimpleGraph.compl_adj]

/-- Minimum degree turns the exact accounting identity into a star lower bound. -/
theorem minimum_degree_accounting (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hm : ∀ v, G.degree x ≤ G.degree v) :
    edgeCount G (Gᶜ.neighborFinset x) + (G.degree x)^2 ≤
      G.edgeFinset.card + edgeCount G (G.neighborFinset x) := by
  have hs := Finset.sum_le_sum (s := G.neighborFinset x) (fun v _ => hm v)
  simp only [Finset.sum_const, G.card_neighborFinset_eq_degree, smul_eq_mul] at hs
  have hid := neighborhood_accounting G x
  nlinarith

lemma edgeCount_restrict_color (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) :
    (colorGraph (restrictColor c S) k).edgeFinset.card = edgeCount (colorGraph c k) S := by
  let iso : colorGraph (restrictColor c S) k ≃g
      (colorGraph c k).comap (Subtype.val : ↥S → V) :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        change (colorGraph c k).Adj a.val b.val ↔ (colorGraph (restrictColor c S) k).Adj a b
        rw [colorGraph_restrict]
        rfl }
  exact iso.card_edgeFinset_eq.trans (edgeCount_induced (colorGraph c k) S)

lemma edgeCount_delete_vertex (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    edgeCount G (Finset.univ.erase x) + G.degree x = G.edgeFinset.card := by
  rw [edgeCount_eq_filter_edgeFinset]
  have hfilter : G.edgeFinset.filter (fun e => e ∈ (Finset.univ.erase x).sym2) =
      G.edgeFinset.filter (fun e => x ∉ e) := by
    apply Finset.filter_congr
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v => simp [Finset.mk_mem_sym2_iff,Sym2.mem_iff,ne_comm]
  rw [hfilter,← G.card_incidenceFinset_eq_degree,G.incidenceFinset_eq_filter]
  simpa only [not_not] using Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => x ∉ e)

lemma restrict_compl_cliqueFree (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) {a : Nat}
    (ha : (colorGraph c k)ᶜ.CliqueFree a) :
    (colorGraph (restrictColor c S) k)ᶜ.CliqueFree a := by
  rw [compl_colorGraph_restrict]
  exact Erdos617.R6.Brooks.cliqueFree_comap _ _ ha

end JSP500
