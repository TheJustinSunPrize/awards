import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Push
import JSP500.WeightedArithmetic

/-!
A counting replacement for the exhaustive weighted light-edge check.
The statement is stronger than the seven-vertex version: the vertex type is
arbitrary finite, and the hypothesis is simply that no one vertex covers all edges.
-/

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def NoSingleCover : Prop :=
  ∀ w : V, ∃ u v, G.Adj u v ∧ u ≠ w ∧ v ≠ w

lemma incidence_inter_card_le_one {u v : V} (h : u ≠ v) :
    (G.incidenceFinset u ∩ G.incidenceFinset v).card ≤ 1 := by
  calc
    _ ≤ ({s(u, v)} : Finset (Sym2 V)).card := by
      apply Finset.card_le_card
      intro e he
      apply Finset.mem_singleton.mpr
      exact G.incidenceSet_inter_incidenceSet_subset h
        ⟨G.mem_incidenceFinset.mp (Finset.mem_inter.mp he).1,
         G.mem_incidenceFinset.mp (Finset.mem_inter.mp he).2⟩
    _ = 1 := Finset.card_singleton _

lemma three_degrees_le {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    G.degree u + G.degree v + G.degree w ≤ G.edgeFinset.card + 3 := by
  let A := G.incidenceFinset u
  let B := G.incidenceFinset v
  let C := G.incidenceFinset w
  have hab := incidence_inter_card_le_one G huv
  have hac := incidence_inter_card_le_one G huw
  have hbc := incidence_inter_card_le_one G hvw
  have hc : ((A ∪ B) ∩ C).card ≤ 2 := by
    have heq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, or_and_right]
    rw [heq]
    have := Finset.card_union_le (A ∩ C) (B ∩ C)
    change (A ∩ C).card ≤ 1 at hac
    change (B ∩ C).card ≤ 1 at hbc
    omega
  have hsub : A ∪ B ∪ C ⊆ G.edgeFinset := by
    exact Finset.union_subset (Finset.union_subset
      (G.incidenceFinset_subset u) (G.incidenceFinset_subset v))
      (G.incidenceFinset_subset w)
  have hcard := Finset.card_le_card hsub
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  change (A ∩ B).card ≤ 1 at hab
  have ha : A.card = G.degree u := G.card_incidenceFinset_eq_degree u
  have hb : B.card = G.degree v := G.card_incidenceFinset_eq_degree v
  have hcc : C.card = G.degree w := G.card_incidenceFinset_eq_degree w
  omega

lemma three_weights_le (z : V → Nat) {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    z u + z v + z w ≤ ∑ x, z x := by
  have h := Finset.sum_le_sum_of_subset
    (f := z) (Finset.subset_univ ({u, v, w} : Finset V))
  simpa [huv, huw, hvw, Nat.add_assoc] using h

lemma edge_bound_cover (H L : Finset V)
    (hends : ∀ u v, G.Adj u v →
      (u ∈ H ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ L) ∨ (u ∈ L ∧ v ∈ H)) :
    G.edgeFinset.card ≤ H.card * (H.card - 1) / 2 + H.card * L.card := by
  let A := H.offDiag.image Sym2.mk.uncurry
  let B := (H ×ˢ L).image (fun p : V × V => s(p.1, p.2))
  have hsub : G.edgeFinset ⊆ A ∪ B := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hadj : G.Adj u v := by simpa using he
      rcases hends u v hadj with h | h | h
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(u,v), by simp [Finset.mem_offDiag, h.1, h.2, hadj.ne], rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(u,v), by simp [h.1,h.2], rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(v,u), by simp [h.1,h.2], Sym2.eq_swap⟩
  have ha : A.card = H.card * (H.card - 1) / 2 := by
    simpa only [A, Nat.choose_two_right] using Sym2.card_image_offDiag H
  have hb : B.card ≤ H.card * L.card := by
    simpa [B] using Finset.card_image_le (s := H ×ˢ L) (f := fun p : V × V => s(p.1,p.2))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le A B
  omega

lemma weighted_degree_sum (z : V → Nat) :
    (∑ v, (G.degree v + z v)) = 2 * G.edgeFinset.card + ∑ v, z v := by
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges]

lemma weighted_degree_at_most_four (z : V → Nat) (bound : Nat)
    (hcover : NoSingleCover G) (hb : G.edgeFinset.card + ∑ v, z v ≤ bound + 2)
    (hheavy : ∀ u v, G.Adj u v → bound < G.degree u + G.degree v + z u + z v) :
    ∀ w, G.degree w + z w ≤ 4 := by
  intro w
  by_contra hw
  have hw' : 5 ≤ G.degree w + z w := by omega
  obtain ⟨u,v,hadj,huw,hvw⟩ := hcover w
  have hd := three_degrees_le G hadj.ne huw hvw
  have hz := three_weights_le z hadj.ne huw hvw
  have := WeightedArithmetic.high_weighted_degree
    G.edgeFinset.card (∑ v,z v) (G.degree w) (z w)
    (G.degree u) (G.degree v) (z u) (z v) bound hb hw' hd hz
  have := hheavy u v hadj
  omega

lemma cover_card_at_least_two (H : Finset V) (hm : 0 < G.edgeFinset.card)
    (hcover : NoSingleCover G)
    (htouch : ∀ u v, G.Adj u v → u ∈ H ∨ v ∈ H) : 2 ≤ H.card := by
  by_contra hh
  have hle : H.card ≤ 1 := by omega
  have hbot : G ≠ ⊥ := by intro he; simp [he] at hm
  obtain ⟨u,v,huv⟩ := G.ne_bot_iff_exists_adj.mp hbot
  have hex : H.Nonempty := by
    rcases htouch u v huv with h | h
    · exact ⟨u,h⟩
    · exact ⟨v,h⟩
  obtain ⟨w,hw⟩ := hex
  obtain ⟨a,b,hab,haw,hbw⟩ := hcover w
  rcases htouch a b hab with ha | hb
  · exact haw (Finset.card_le_one.mp hle a ha w hw)
  · exact hbw (Finset.card_le_one.mp hle b hb w hw)

theorem weighted_light_edge_seven (z : V → Nat) (hcover : NoSingleCover G)
    (hm : 6 ≤ G.edgeFinset.card) (hb : G.edgeFinset.card + ∑ v, z v ≤ 9) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v + z u + z v ≤ 7 := by
  classical
  by_contra h
  push Not at h
  have hD := weighted_degree_at_most_four G z 7 hcover hb h
  let H : Finset V := Finset.univ.filter (fun v => G.degree v + z v = 4)
  have hends : ∀ u v, G.Adj u v → u ∈ H ∧ v ∈ H := by
    intro u v huv
    have := h u v huv
    have := hD u
    have := hD v
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have he := edge_bound_cover G H ∅ (fun u v huv => Or.inl (hends u v huv))
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at he
  have hsum : 4 * H.card ≤ 2 * G.edgeFinset.card + ∑ v, z v := by
    have hx : (∑ v ∈ H, (G.degree v + z v)) = 4 * H.card := by
      calc
        _ = ∑ _v ∈ H, 4 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = _ := by simp [Nat.mul_comm]
    have hy := Finset.sum_le_sum_of_subset
      (f := fun v => G.degree v + z v) (Finset.subset_univ H)
    rw [hx, weighted_degree_sum G z] at hy
    exact hy
  exact WeightedArithmetic.budget_nine_impossible _ _ _ hm hb hsum he

theorem weighted_light_edge_six (z : V → Nat) (hcover : NoSingleCover G)
    (hm : 6 ≤ G.edgeFinset.card) (hb : G.edgeFinset.card + ∑ v, z v ≤ 8) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v + z u + z v ≤ 6 := by
  classical
  by_contra h
  push Not at h
  have hD := weighted_degree_at_most_four G z 6 hcover hb h
  let H : Finset V := Finset.univ.filter (fun v => G.degree v + z v = 4)
  let L : Finset V := Finset.univ.filter (fun v => G.degree v + z v = 3)
  have hends : ∀ u v, G.Adj u v →
      (u ∈ H ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ L) ∨ (u ∈ L ∧ v ∈ H) := by
    intro u v huv
    have := h u v huv
    have := hD u
    have := hD v
    simp only [H, L, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have he := edge_bound_cover G H L hends
  have hh : 2 ≤ H.card := cover_card_at_least_two G H (by omega) hcover (by
    intro u v huv
    rcases hends u v huv with h | h | h
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inr h.2)
  have hdis : Disjoint H L := by
    apply Finset.disjoint_left.mpr
    intro v hvh hvl
    have := (Finset.mem_filter.mp hvh).2
    have := (Finset.mem_filter.mp hvl).2
    omega
  have hsum : 4 * H.card + 3 * L.card ≤ 2 * G.edgeFinset.card + ∑ v, z v := by
    have hx : (∑ v ∈ H, (G.degree v + z v)) = 4 * H.card := by
      calc
        _ = ∑ _v ∈ H, 4 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = _ := by simp [Nat.mul_comm]
    have hy : (∑ v ∈ L, (G.degree v + z v)) = 3 * L.card := by
      calc
        _ = ∑ _v ∈ L, 3 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = _ := by simp [Nat.mul_comm]
    have hz := Finset.sum_le_sum_of_subset
      (f := fun v => G.degree v + z v) (Finset.subset_univ (H ∪ L))
    rw [Finset.sum_union hdis, hx, hy, weighted_degree_sum G z] at hz
    exact hz
  exact WeightedArithmetic.budget_eight_impossible _ _ _ _ hm hb hh hsum he

end JSP500
