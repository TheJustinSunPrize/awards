import JSP500.CliquePeeling

open Finset
open scoped BigOperators Classical

namespace JSP500

def OrderExcluded (a n : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : Sym2 V → Fin 7), Balanced c →
    n ≤ Fintype.card V → ∀ k, (colorGraph c k)ᶜ.CliqueFree (a+1) → False

def ColorFloor (a n b : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : Sym2 V → Fin 7), Balanced c →
    Fintype.card V = n → ∀ k, (colorGraph c k)ᶜ.CliqueFree (a+1) →
    b ≤ (colorGraph c k).edgeFinset.card

lemma order_one : OrderExcluded 1 8 := by
  intro V _ _ c hb hn k ha
  have hbot := SimpleGraph.cliqueFree_two.mp ha
  have ht : colorGraph c k = ⊤ := by
    have h := congrArg (fun G : SimpleGraph V => Gᶜ) hbot
    simpa only [compl_compl,compl_bot] using h
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (show 8 ≤ (Finset.univ : Finset V).card by simpa using hn)
  apply balanced_colorGraph_cliqueFree c hb k S
  refine ⟨?_,hS⟩
  rw [ht]
  exact SimpleGraph.IsClique.top _

lemma order_peel_step (a n t q : Nat) (ih : OrderExcluded a t)
    (hc : CoreExcluded (a+1) q) (hqn : q ≤ n) (htn : t+7 ≤ n) (ha6 : a+1 ≤ 6) :
    OrderExcluded (a+1) n := by
  intro V _ _ c hb hn k ha
  by_cases ho : (colorGraph c k).CliqueFree 7
  · exact hc V c hb (by omega) k ha ho
  · simp only [SimpleGraph.CliqueFree,not_forall,not_not] at ho
    obtain ⟨B,hB⟩ := ho
    let R := Finset.univ \ B
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [Finset.card_univ,hB.card_eq] at hcard
    apply ih ↥R (restrictColor c R) (balanced_restrict c hb R)
      (by rw [Fintype.card_coe]; change t ≤ (Finset.univ \ B).card; omega) k
    exact clique_deletion_alpha c hb k ha6 ha B hB

lemma order_two : OrderExcluded 2 15 :=
  order_peel_step 1 15 8 14 order_one core_two (by decide) (by decide) (by decide)

lemma order_three : OrderExcluded 3 22 :=
  order_peel_step 2 22 15 22 order_two core_three (by decide) (by decide) (by decide)

lemma color_floor_four_twenty_nine : ColorFloor 4 29 113 := by
  intro V _ _ c hb hn k ha
  by_cases ho : (colorGraph c k).CliqueFree 7
  · exact floor_four_twenty_nine V c hb hn k ha ho
  · simp only [SimpleGraph.CliqueFree,not_forall,not_not] at ho
    obtain ⟨B,hB⟩ := ho
    let R := Finset.univ \ B
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [Finset.card_univ,hn,hB.card_eq] at hcard
    exact False.elim (order_three ↥R (restrictColor c R) (balanced_restrict c hb R)
      (by rw [Fintype.card_coe]; change 22 ≤ (Finset.univ \ B).card; omega) k
      (clique_deletion_alpha c hb k (by decide) ha B hB))

lemma color_floor_peel_step (a n b d : Nat) (ha6 : a+1 ≤ 6)
    (hf : EdgeFloor (a+1) n b) (ih : ColorFloor a (n-7) d) (hbd : b ≤ d+21) :
    ColorFloor (a+1) n b := by
  intro V _ _ c hb hn k ha
  by_cases ho : (colorGraph c k).CliqueFree 7
  · exact hf V c hb hn k ha ho
  · simp only [SimpleGraph.CliqueFree,not_forall,not_not] at ho
    obtain ⟨B,hB⟩ := ho
    let R := Finset.univ \ B
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [Finset.card_univ,hn,hB.card_eq] at hcard
    have hr := ih ↥R (restrictColor c R) (balanced_restrict c hb R)
      (by rw [Fintype.card_coe]; change (Finset.univ \ B).card = n-7; omega) k
      (clique_deletion_alpha c hb k ha6 ha B hB)
    rw [edgeCount_restrict_color] at hr
    have hd : Disjoint B R := by
      apply Finset.disjoint_left.mpr
      intro v hvB hvR
      exact (Finset.mem_sdiff.mp hvR).2 hvB
    have he := edgeCount_disjoint_le_total (colorGraph c k) hd
    rw [edgeCount_clique _ hB.isClique,hB.card_eq] at he
    norm_num only [Nat.choose_two_right] at he
    omega

lemma color_floor_five_thirty_six : ColorFloor 5 36 134 :=
  color_floor_peel_step 4 36 134 113 (by decide) floor_five_thirty_six
    color_floor_four_twenty_nine (by decide)

lemma color_floor_six_forty_three : ColorFloor 6 43 155 := by
  apply color_floor_peel_step 5 43 155 134 (by decide) _ color_floor_five_thirty_six (by decide)
  intro V _ _ c hb hn k ha ho
  have h := floor_six_forty_three V c hb hn k ha ho
  omega

/-- Lift an unconditional color-graph edge floor by deleting each vertex and
summing the resulting inequalities. -/
lemma color_floor_lift (a n b d : Nat) (hn : 1 ≤ n) (ih : ColorFloor a n b)
    (hd : 1 ≤ d) (hgap : (n-1)*(d-1) < (n+1)*b) : ColorFloor a (n+1) d := by
  intro V _ _ c hb hcard k ha
  by_contra he
  have hv : ∀ x : V, b + (colorGraph c k).degree x ≤ (colorGraph c k).edgeFinset.card := by
    intro x
    let R := (Finset.univ : Finset V).erase x
    have hr := ih ↥R (restrictColor c R) (balanced_restrict c hb R)
      (by simp only [Fintype.card_coe,R,Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,hcard]; omega)
      k (restrict_compl_cliqueFree c R k ha)
    rw [edgeCount_restrict_color] at hr
    have hx := edgeCount_delete_vertex (colorGraph c k) x
    change b ≤ edgeCount (colorGraph c k) (Finset.univ.erase x) at hr
    omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun x _ => hv x)
  simp only [Finset.sum_add_distrib, Finset.sum_const,Finset.card_univ,hcard,smul_eq_mul,
    (colorGraph c k).sum_degrees_eq_twice_card_edges] at hs
  have hlow : n = n-1+1 := by omega
  have hd' : (colorGraph c k).edgeFinset.card ≤ d-1 := by omega
  nlinarith [Nat.mul_le_mul_left (n-1) hd']

lemma color_floor_six_forty_four : ColorFloor 6 44 163 :=
  color_floor_lift 6 43 155 163 (by decide) color_floor_six_forty_three (by decide) (by decide)
lemma color_floor_six_forty_five : ColorFloor 6 45 171 :=
  color_floor_lift 6 44 163 171 (by decide) color_floor_six_forty_four (by decide) (by decide)
lemma color_floor_six_forty_six : ColorFloor 6 46 179 :=
  color_floor_lift 6 45 171 179 (by decide) color_floor_six_forty_five (by decide) (by decide)
lemma color_floor_six_forty_seven : ColorFloor 6 47 187 :=
  color_floor_lift 6 46 179 187 (by decide) color_floor_six_forty_six (by decide) (by decide)
lemma color_floor_six_forty_eight : ColorFloor 6 48 196 :=
  color_floor_lift 6 47 187 196 (by decide) color_floor_six_forty_seven (by decide) (by decide)
lemma color_floor_six_forty_nine : ColorFloor 6 49 205 :=
  color_floor_lift 6 48 196 205 (by decide) color_floor_six_forty_eight (by decide) (by decide)

end JSP500
