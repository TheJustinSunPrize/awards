import JSP500.NeighborhoodWeights

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V : Type} [Fintype V] [DecidableEq V]

lemma neighborhood_pair_lower (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7) (x : V)
    (u v : ↥((colorGraph c k).neighborFinset x))
    (huv : ((colorGraph c k).comap (Subtype.val : ↥((colorGraph c k).neighborFinset x) → V))ᶜ.Adj u v) :
    ((colorGraph c k)ᶜ.neighborFinset x).card ≤ 13 +
      (((colorGraph c k)ᶜ.neighborFinset x).filter (fun w => (colorGraph c k).Adj u w)).card +
      (((colorGraph c k)ᶜ.neighborFinset x).filter (fun w => (colorGraph c k).Adj v w)).card := by
  have huv' : (colorGraph c k)ᶜ.Adj u.val v.val :=
    ⟨fun h => huv.1 (Subtype.ext h),huv.2⟩
  apply pair_cross_degree_lower c hb k ha ho u v huv'
  · intro hu
    have h1 := ((colorGraph c k).mem_neighborFinset x u).mp u.property
    have h2 := ((colorGraph c k)ᶜ.mem_neighborFinset x u).mp hu
    exact h2.2 h1
  · intro hv
    have h1 := ((colorGraph c k).mem_neighborFinset x v).mp v.property
    have h2 := ((colorGraph c k)ᶜ.mem_neighborFinset x v).mp hv
    exact h2.2 h1

/-- The seven-neighbor weighted lemma now rules out the two budgets needed
for P4(28) and P4(29). -/
theorem seven_neighbor_budget_impossible (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7)
    (x : V) (hm : ∀ v, (colorGraph c k).degree x ≤ (colorGraph c k).degree v)
    (hd : (colorGraph c k).degree x = 7) (b : Nat) (hbval : b=6 ∨ b=7)
    (he : (colorGraph c k).edgeFinset.card ≤
      edgeCount (colorGraph c k) ((colorGraph c k)ᶜ.neighborFinset x) + 28 + (b+2))
    (hW : b+14 ≤ ((colorGraph c k)ᶜ.neighborFinset x).card) : False := by
  let G := colorGraph c k
  let N := G.neighborFinset x
  let W := Gᶜ.neighborFinset x
  let H := G.comap (Subtype.val : ↥N → V)
  let M := Hᶜ
  obtain ⟨z,hz,hledger⟩ := weighted_neighborhood_data G x hm
  change ∀ y : ↥N, (W.filter (fun w => G.Adj y w)).card = M.degree y + z y at hz
  change G.edgeFinset.card = edgeCount G W + G.degree x + (G.degree x).choose 2 +
    M.edgeFinset.card + ∑ y, z y at hledger
  have hn : Fintype.card ↥N = 7 := by
    rw [Fintype.card_coe]; exact (G.card_neighborFinset_eq_degree x).trans hd
  have hnedge := neighbor_edge_bound_seven c hb k x hd
  have hi := edgeCount_induced G N
  change H.edgeFinset.card = edgeCount G N at hi
  have hp := edges_add_complement H
  change H.edgeFinset.card + M.edgeFinset.card = (Fintype.card ↥N).choose 2 at hp
  rw [hn] at hp
  norm_num [Nat.choose_two_right] at hp
  have hM : 6 ≤ M.edgeFinset.card := by
    change edgeCount G N ≤ 15 at hnedge
    omega
  have hα : Mᶜ.CliqueFree 6 := by
    simpa only [M, compl_compl] using cliqueFree_neighbor_comap G ho x
  have hcover := noSingleCover_of_seven M hn hα
  have hbudget : M.edgeFinset.card + ∑ y, z y ≤ b+2 := by
    change G.edgeFinset.card ≤ edgeCount G W + 28 + (b+2) at he
    change G.degree x = 7 at hd
    rw [hd] at hledger
    norm_num only [Nat.choose_two_right] at hledger
    omega
  have hlight : ∃ u v, M.Adj u v ∧ M.degree u + M.degree v + z u + z v ≤ b := by
    rcases hbval with rfl | rfl
    · exact weighted_light_edge_six M z hcover hM hbudget
    · exact weighted_light_edge_seven M z hcover hM hbudget
  obtain ⟨u,v,huv,hsmall⟩ := hlight
  have hlower := neighborhood_pair_lower c hb k ha ho x u v huv
  change W.card ≤ 13 + (W.filter (fun w => G.Adj u w)).card +
    (W.filter (fun w => G.Adj v w)).card at hlower
  rw [hz u,hz v] at hlower
  change b+14 ≤ W.card at hW
  omega

lemma weighted_edge_sum_le_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V → Nat) {u v : V} (huv : G.Adj u v) :
    G.degree u + G.degree v + z u + z v ≤ G.edgeFinset.card + 1 + ∑ w, z w := by
  have hi := incidence_inter_card_le_one G huv.ne
  have hu := G.card_incidenceFinset_eq_degree u
  have hv := G.card_incidenceFinset_eq_degree v
  have hc := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
  have hsub := Finset.card_le_card (Finset.union_subset (G.incidenceFinset_subset u) (G.incidenceFinset_subset v))
  have hz := Finset.sum_le_sum_of_subset (f := z) (Finset.subset_univ ({u,v} : Finset V))
  simp only [Finset.sum_pair huv.ne] at hz
  omega

theorem six_neighbor_budget_impossible (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7)
    (ha : (colorGraph c k)ᶜ.CliqueFree 5) (ho : (colorGraph c k).CliqueFree 7)
    (x : V) (hm : ∀ v, (colorGraph c k).degree x ≤ (colorGraph c k).degree v)
    (hd : (colorGraph c k).degree x = 6)
    (he : (colorGraph c k).edgeFinset.card ≤
      edgeCount (colorGraph c k) ((colorGraph c k)ᶜ.neighborFinset x) + 24)
    (hW : 18 ≤ ((colorGraph c k)ᶜ.neighborFinset x).card) : False := by
  let G := colorGraph c k
  let N := G.neighborFinset x
  let W := Gᶜ.neighborFinset x
  let H := G.comap (Subtype.val : ↥N → V)
  let M := Hᶜ
  obtain ⟨z,hz,hledger⟩ := weighted_neighborhood_data G x hm
  change ∀ y : ↥N, (W.filter (fun w => G.Adj y w)).card = M.degree y + z y at hz
  change G.edgeFinset.card = edgeCount G W + G.degree x + (G.degree x).choose 2 +
    M.edgeFinset.card + ∑ y, z y at hledger
  have hn : Fintype.card ↥N = 6 := by
    rw [Fintype.card_coe]; exact (G.card_neighborFinset_eq_degree x).trans hd
  have hnedge := neighbor_edge_bound_six G x ho hd
  have hi := edgeCount_induced G N
  change H.edgeFinset.card = edgeCount G N at hi
  have hp := edges_add_complement H
  change H.edgeFinset.card + M.edgeFinset.card = (Fintype.card ↥N).choose 2 at hp
  rw [hn] at hp
  norm_num [Nat.choose_two_right] at hp
  have hM : 0 < M.edgeFinset.card := by
    change edgeCount G N ≤ 14 at hnedge
    omega
  have hbot : M ≠ ⊥ := by intro h; simp [h] at hM
  obtain ⟨u,v,huv⟩ := M.ne_bot_iff_exists_adj.mp hbot
  have hsmall := weighted_edge_sum_le_total M z huv
  have hlower := neighborhood_pair_lower c hb k ha ho x u v huv
  change W.card ≤ 13 + (W.filter (fun w => G.Adj u w)).card +
    (W.filter (fun w => G.Adj v w)).card at hlower
  rw [hz u,hz v] at hlower
  change G.degree x = 6 at hd
  rw [hd] at hledger
  norm_num only [Nat.choose_two_right] at hledger
  change G.edgeFinset.card ≤ edgeCount G W + 24 at he
  change 18 ≤ W.card at hW
  simp only [Finset.sum_coe_sort_eq_attach] at hsmall hledger
  dsimp only [N,H,M] at hsmall hledger hlower
  omega

end JSP500
