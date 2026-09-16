import JSP500.GraphAccounting

set_option maxHeartbeats 800000

open Finset
open scoped BigOperators Classical

namespace JSP500

/-- A lower edge bound for actual balanced color graphs, with specified order
and independence bound, excluding a seven-clique. -/
def EdgeFloor (a n b : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : Sym2 V → Fin 7), Balanced c →
    Fintype.card V = n → ∀ k,
    (colorGraph c k)ᶜ.CliqueFree (a+1) → (colorGraph c k).CliqueFree 7 →
    b ≤ (colorGraph c k).edgeFinset.card

variable {V : Type} [Fintype V] [DecidableEq V]

lemma least_degree_vertex (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 0 < Fintype.card V) :
    ∃ v, ∀ w, G.degree v ≤ G.degree w := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
  exact ⟨v, fun w => hv ▸ G.minDegree_le_degree w⟩

lemma minimum_degree_average (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hm : ∀ v, G.degree x ≤ G.degree v) :
    Fintype.card V * G.degree x ≤ 2*G.edgeFinset.card := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hm v)
  simpa [G.sum_degrees_eq_twice_card_edges] using h

lemma nonneighbor_alpha_drop (c : Sym2 V → Fin 7) (k : Fin 7) (x : V) {a : Nat}
    (ha : (colorGraph c k)ᶜ.CliqueFree (a+2)) :
    (colorGraph (restrictColor c ((colorGraph c k)ᶜ.neighborFinset x)) k)ᶜ.CliqueFree (a+1) := by
  rw [compl_colorGraph_restrict]
  exact cliqueFree_neighbor_comap _ ha x

lemma nonneighbor_clique_bound (c : Sym2 V → Fin 7) (k : Fin 7) (x : V)
    (ho : (colorGraph c k).CliqueFree 7) :
    (colorGraph (restrictColor c ((colorGraph c k)ᶜ.neighborFinset x)) k).CliqueFree 7 := by
  rw [colorGraph_restrict]
  exact Erdos617.R6.Brooks.cliqueFree_comap _ _ ho

lemma nonneighbor_card (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Fintype.card ↥(Gᶜ.neighborFinset x) = Fintype.card V - 1 - G.degree x := by
  rw [Fintype.card_coe, Gᶜ.card_neighborFinset_eq_degree, G.degree_compl]

lemma nonneighbor_order_lt_core (c : Sym2 V → Fin 7) (hb : Balanced c)
    (k : Fin 7) (x : V) {a t : Nat} (hc : CoreExcluded a t)
    (ha : (colorGraph c k)ᶜ.CliqueFree (a+2))
    (ho : (colorGraph c k).CliqueFree 7) :
    Fintype.card V - 1 - (colorGraph c k).degree x < t := by
  by_contra h
  exact hc _ (restrictColor c _) (balanced_restrict c hb _)
    (by rw [nonneighbor_card]; omega) k (nonneighbor_alpha_drop c k x ha)
    (nonneighbor_clique_bound c k x ho)

lemma floor_on_nonneighbors (c : Sym2 V → Fin 7) (hb : Balanced c)
    (k : Fin 7) (x : V) {a n b : Nat} (hf : EdgeFloor a n b)
    (ha : (colorGraph c k)ᶜ.CliqueFree (a+2)) (ho : (colorGraph c k).CliqueFree 7)
    (hn : Fintype.card V - 1 - (colorGraph c k).degree x = n) :
    b ≤ edgeCount (colorGraph c k) ((colorGraph c k)ᶜ.neighborFinset x) := by
  have h := hf _ (restrictColor c _) (balanced_restrict c hb _)
    (by rw [nonneighbor_card]; exact hn) k (nonneighbor_alpha_drop c k x ha)
    (nonneighbor_clique_bound c k x ho)
  let S := (colorGraph c k)ᶜ.neighborFinset x
  let iso : colorGraph (restrictColor c S) k ≃g
      (colorGraph c k).comap (Subtype.val : ↥S → V) :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        change (colorGraph c k).Adj a.val b.val ↔
          (colorGraph (restrictColor c S) k).Adj a b
        rw [colorGraph_restrict]
        rfl }
  have hc := iso.card_edgeFinset_eq
  have he := edgeCount_induced (colorGraph c k) S
  change b ≤ (colorGraph (restrictColor c S) k).edgeFinset.card at h
  change b ≤ edgeCount (colorGraph c k) S
  omega

lemma neighbor_edge_bound_six (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (ho : G.CliqueFree 7) (hd : G.degree x = 6) : edgeCount G (G.neighborFinset x) ≤ 14 := by
  by_contra h
  have hcard : (G.neighborFinset x).card = 6 := by rw [G.card_neighborFinset_eq_degree, hd]
  have hcl : G.IsNClique 6 (G.neighborFinset x) := by
    refine ⟨?_,hcard⟩
    intro u hu v hv huv
    exact adj_of_edgeCount_choose G _ (by rw [hcard]; norm_num [Nat.choose_two_right]; omega) hu hv huv
  exact ho _ (hcl.insert (a := x) (fun v hv => (G.mem_neighborFinset x v).mp hv))

lemma neighbor_edge_bound_seven (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (x : V) (hd : (colorGraph c k).degree x = 7) :
    edgeCount (colorGraph c k) ((colorGraph c k).neighborFinset x) ≤ 15 := by
  let G := colorGraph c k
  have hx : x ∉ G.neighborFinset x := by simp
  have hn : (G.neighborFinset x).card = 7 := by rw [G.card_neighborFinset_eq_degree]; exact hd
  have h := edgeCount_add_card_le_insert G (Finset.Subset.refl _) hx
  have hcap := local_cap_twenty_two c hb (insert x (G.neighborFinset x))
    (by rw [Finset.card_insert_of_notMem hx, hn]) k
  rw [← edgeCount_color] at hcap
  change edgeCount G _ ≤ 22 at hcap
  change edgeCount G (G.neighborFinset x) ≤ 15
  omega

/-- Star bounds needed in this fixed case, for degrees zero through seven. -/
def starSmall (d : Nat) : Nat := if d=6 then 22 else if d=7 then 34 else (d+1).choose 2

lemma star_small_bound (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7) (x : V)
    (hm : ∀ v, (colorGraph c k).degree x ≤ (colorGraph c k).degree v)
    (ho : (colorGraph c k).CliqueFree 7) (hd : (colorGraph c k).degree x ≤ 7) :
    edgeCount (colorGraph c k) ((colorGraph c k)ᶜ.neighborFinset x) +
      starSmall ((colorGraph c k).degree x) ≤ (colorGraph c k).edgeFinset.card := by
  have h := minimum_degree_accounting (colorGraph c k) x hm
  have ht := edgeCount_le_choose_two (colorGraph c k) ((colorGraph c k).neighborFinset x)
  rw [(colorGraph c k).card_neighborFinset_eq_degree] at ht
  by_cases h6 : (colorGraph c k).degree x = 6
  · have hN := neighbor_edge_bound_six (colorGraph c k) x ho h6
    simp only [h6, starSmall, ite_true] at h ⊢
    norm_num at h
    omega
  by_cases h7 : (colorGraph c k).degree x = 7
  · have hN := neighbor_edge_bound_seven c hb k x h7
    simp only [h7, starSmall] at h ⊢
    norm_num at h ⊢
    omega
  have hd5 : (colorGraph c k).degree x ≤ 5 := by omega
  interval_cases hh : (colorGraph c k).degree x <;>
    norm_num [starSmall, Nat.choose_two_right] at h ht ⊢ <;> omega

/-- KP gives the only scalar base needed for the small direct proof. -/
theorem floor_two_thirteen : EdgeFloor 2 13 41 := by
  intro V _ _ c _ hn k ha ho
  have hnc : ¬ (colorGraph c k)ᶜ.Colorable 2 := by
    intro hc
    have h := card_le_of_colorable_and_independence hc (by simpa using ho)
    omega
  have h := kp_saving_finite (colorGraph c k)ᶜ 2 (by decide) (by omega) ha hnc
  have ht := edges_add_complement (colorGraph c k)
  rw [hn] at h ht
  norm_num [SimpleGraph.turanNumber_eq, Nat.choose_two_right] at h ht
  omega

end JSP500
