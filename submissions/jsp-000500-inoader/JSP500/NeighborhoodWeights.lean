import JSP500.PairCover

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V : Type} [Fintype V] [DecidableEq V]

lemma degree_comap_subtype (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (y : ↥S) :
    (G.comap (Subtype.val : ↥S → V)).degree y = (S.filter (fun w => G.Adj y w)).card := by
  rw [← (G.comap (Subtype.val : ↥S → V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨w.property, by simpa using hw⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro w hw
    obtain ⟨hwS,hadj⟩ := Finset.mem_filter.mp hw
    exact ⟨⟨w,hwS⟩,by simpa using hadj,rfl⟩

/-- Partition the degree of a neighbor into its edge to x, edges inside N(x),
and edges to the nonneighbors of x. -/
lemma neighbor_degree_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : G.Adj x y) :
    G.degree y = 1 + ((G.neighborFinset x).filter (fun w => G.Adj y w)).card +
      ((Gᶜ.neighborFinset x).filter (fun w => G.Adj y w)).card := by
  let A := (G.neighborFinset x).filter (fun w => G.Adj y w)
  let B := (Gᶜ.neighborFinset x).filter (fun w => G.Adj y w)
  have hx : x ∉ A ∪ B := by simp [A,B]
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    have hw1 : G.Adj x w := by simpa [A] using (Finset.mem_filter.mp hwA).1
    have hw2 : ¬G.Adj x w := (by simpa using (Finset.mem_filter.mp hwB).1 : x ≠ w ∧ ¬G.Adj x w).2
    exact hw2 hw1
  have heq : G.neighborFinset y = insert x (A ∪ B) := by
    ext w
    by_cases hw : w = x
    · subst w
      simp [hxy.symm]
    · by_cases hxw : G.Adj x w <;>
        simp [A,B,SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,hw,Ne.symm hw,hxw]
  rw [← G.card_neighborFinset_eq_degree, heq, Finset.card_insert_of_notMem hx,
    Finset.card_union_of_disjoint hd]
  dsimp only [A,B]
  omega

/-- For a minimum-degree vertex, each neighbor has at least its complementary
internal degree worth of neighbors outside the closed neighborhood. -/
lemma complementary_degree_le_cross (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hm : ∀ v, G.degree x ≤ G.degree v) (y : ↥(G.neighborFinset x)) :
    (G.comap (Subtype.val : ↥(G.neighborFinset x) → V))ᶜ.degree y ≤
      ((Gᶜ.neighborFinset x).filter (fun w => G.Adj y w)).card := by
  let H := G.comap (Subtype.val : ↥(G.neighborFinset x) → V)
  have hp := neighbor_degree_partition G x y ((G.mem_neighborFinset x y).mp y.property)
  have hm' := hm y
  have hd := H.degree_compl (v := y)
  have hn : Fintype.card ↥(G.neighborFinset x) = G.degree x := by
    rw [Fintype.card_coe, G.card_neighborFinset_eq_degree]
  have hi := degree_comap_subtype G (G.neighborFinset x) y
  change H.degree y = _ at hi
  rw [hn] at hd
  change Hᶜ.degree y ≤ _
  omega

/-- Exact weighted-neighborhood ledger. The weights are cross-degree excesses;
no external arithmetic certificate or unproved graph premise is used. -/
theorem weighted_neighborhood_data (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hm : ∀ v, G.degree x ≤ G.degree v) :
    let N := G.neighborFinset x
    let W := Gᶜ.neighborFinset x
    let M := (G.comap (Subtype.val : ↥N → V))ᶜ
    ∃ z : ↥N → Nat,
      (∀ y : ↥N, (W.filter (fun w => G.Adj y w)).card = M.degree y + z y) ∧
      G.edgeFinset.card = edgeCount G W + G.degree x + (G.degree x).choose 2 +
        M.edgeFinset.card + ∑ y, z y := by
  dsimp only
  let N := G.neighborFinset x
  let W := Gᶜ.neighborFinset x
  let H := G.comap (Subtype.val : ↥N → V)
  let M := Hᶜ
  let cross : ↥N → Nat := fun y => (W.filter (fun w => G.Adj y w)).card
  let z : ↥N → Nat := fun y => cross y - M.degree y
  have hcross : ∀ y, cross y = M.degree y + z y := by
    intro y
    have h := complementary_degree_le_cross G x hm y
    change M.degree y ≤ cross y at h
    dsimp only [z]
    omega
  refine ⟨z,hcross,?_⟩
  have hsumcross : (∑ y, cross y) = 2*M.edgeFinset.card + ∑ y, z y := by
    simp_rw [hcross]
    rw [Finset.sum_add_distrib, M.sum_degrees_eq_twice_card_edges]
  have hn : Fintype.card ↥N = G.degree x := by
    rw [Fintype.card_coe]; exact G.card_neighborFinset_eq_degree x
  have hpartition : (∑ y : ↥N, G.degree y) =
      G.degree x + 2*H.edgeFinset.card + ∑ y, cross y := by
    calc
      _ = ∑ y : ↥N, (1 + H.degree y + cross y) := by
        apply Finset.sum_congr rfl
        intro y _
        have h := neighbor_degree_partition G x y ((G.mem_neighborFinset x y).mp y.property)
        have hi := degree_comap_subtype G N y
        change H.degree y = _ at hi
        change G.degree y = 1 + H.degree y + cross y
        rw [hi]
        exact h
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          H.sum_degrees_eq_twice_card_edges]
        simp [N]
  have hs : (∑ y : ↥N, G.degree y) = ∑ y ∈ N, G.degree y := Finset.sum_coe_sort N (fun y : V => G.degree y)
  have he := edgeCount_induced G N
  change H.edgeFinset.card = edgeCount G N at he
  have hp := edges_add_complement H
  change H.edgeFinset.card + M.edgeFinset.card = (Fintype.card ↥N).choose 2 at hp
  rw [hn] at hp
  have hid := neighborhood_accounting G x
  change edgeCount G W + (∑ y ∈ N, G.degree y) = G.edgeFinset.card + edgeCount G N at hid
  change G.edgeFinset.card = edgeCount G W + G.degree x + (G.degree x).choose 2 +
    M.edgeFinset.card + ∑ y, z y
  omega

end JSP500
