import Statement

open scoped BigOperators
open Finset

namespace JSP000840

set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev TriangleCount {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : Nat :=
  #(G.cliqueFinset 3)

lemma floor_sq_sub (n : ℕ) (hn : 4 ≤ n) :
    (n - 2) ^ 2 / 4 = n ^ 2 / 4 - n + 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hnrep : n = 2 * (n / 2) := by omega
    rw [hnrep]
    let k := n / 2
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hminus : 2 * k - 2 = 2 * (k - 1) := by omega
    change (2 * k - 2) ^ 2 / 4 = (2 * k) ^ 2 / 4 - 2 * k + 1
    rw [hminus]
    have hleft : (2 * (k - 1)) ^ 2 / 4 = (k - 1)^2 := by
      rw [show (2 * (k - 1)) ^ 2 = 4 * (k - 1)^2 by ring]
      exact Nat.mul_div_right _ (by norm_num)
    have hright : (2 * k) ^ 2 / 4 = k^2 := by
      rw [show (2 * k) ^ 2 = 4 * k^2 by ring]
      exact Nat.mul_div_right _ (by norm_num)
    rw [hleft, hright]
    have h2k : 2*k ≤ k^2 := by nlinarith
    rw [← Nat.sub_add_comm h2k]
    have h2k' : 2*k ≤ k^2 + 1 := le_trans h2k (Nat.le_add_right _ _)
    let j := k - 1
    have hkrep : k = j + 1 := by dsimp [j]; omega
    have hsub : k^2 + 1 - 2*k = j^2 := by
      apply (Nat.sub_eq_iff_eq_add h2k').2
      rw [hkrep]
      change (j + 1)^2 + 1 = j^2 + 2 * (j + 1)
      ring
    change j^2 = k^2 + 1 - 2*k
    rw [hsub]
  · have hnrep : n = 2 * (n / 2) + 1 := by omega
    rw [hnrep]
    let k := n / 2
    have hk : 2 ≤ k := by dsimp [k]; omega
    change (2 * k + 1 - 2) ^ 2 / 4 = (2 * k + 1) ^ 2 / 4 - (2*k+1) + 1
    have hminus : 2 * k + 1 - 2 = 2 * (k - 1) + 1 := by omega
    rw [hminus]
    have hleft : (2 * (k - 1) + 1) ^ 2 / 4 = (k - 1) * k := by
      have hsq : (2 * (k - 1) + 1) ^ 2 = 4 * (k - 1) * k + 1 := by
        have h : k-1+1=k := Nat.sub_add_cancel (by omega : 1≤k)
        nlinarith
      rw [hsq]
      apply Nat.div_eq_of_lt_le <;> nlinarith
    have hright : (2 * k + 1) ^ 2 / 4 = k * (k + 1) := by
      have hsq : (2 * k + 1)^2 = 4 * k * (k + 1) + 1 := by ring
      rw [hsq]
      apply Nat.div_eq_of_lt_le <;> nlinarith
    rw [hleft, hright]
    have hY : 2*k+1 ≤ k*(k+1) := by nlinarith
    rw [← Nat.sub_add_comm hY]
    have hY' : 2*k+1 ≤ k*(k+1)+1 := le_trans hY (Nat.le_add_right _ _)
    have hsub : k*(k+1)+1-(2*k+1) = (k-1)*k := by
      apply (Nat.sub_eq_iff_eq_add hY').2
      change k*(k+1)+1 = (k-1)*k + (2*k+1)
      have h : k-1+1=k := Nat.sub_add_cancel (by omega : 1≤k)
      nlinarith
    rw [hsub]

lemma floor_sq_sub_one (n : ℕ) :
    (n - 1) ^ 2 / 4 = n ^ 2 / 4 - n / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hnrep : n = 2 * (n / 2) := by omega
    rw [hnrep]
    let k := n / 2
    have hdiv : (2 * k) / 2 = k := by omega
    change (2*k -1)^2 /4 = (2*k)^2/4 - (2*k)/2
    rw [hdiv]
    have hleft : (2*k-1)^2 /4 = k*(k-1) := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hk1 : 1 ≤ k := by omega
        have hsq : (2*k-1)^2 = 4*k*(k-1)+1 := by
          have hm : 2*k-1=2*(k-1)+1 := by omega
          rw [hm]
          have h : k-1+1=k := Nat.sub_add_cancel hk1
          nlinarith
        rw [hsq]
        apply Nat.div_eq_of_lt_le <;> nlinarith
    have hright : (2*k)^2/4=k^2 := by
      rw [show (2*k)^2=4*k^2 by ring]
      exact Nat.mul_div_right _ (by norm_num)
    rw [hleft, hright]
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk1 : 1≤k := by omega
      have hkle : k ≤ k^2 := by nlinarith
      have hs : k^2-k = k*(k-1) := by
        apply (Nat.sub_eq_iff_eq_add hkle).2
        have h : k-1+1=k := Nat.sub_add_cancel hk1
        nlinarith
      exact hs.symm
  · have hnrep : n = 2 * (n / 2)+1 := by omega
    rw [hnrep]
    let k := n /2
    have hdiv : (2 * k +1) /2 = k := by omega
    change (2*k+1-1)^2/4 = (2*k+1)^2/4 - (2*k+1)/2
    rw [hdiv]
    simp only [Nat.add_sub_cancel]
    have hleft : (2*k)^2/4=k^2 := by
      rw [show (2*k)^2=4*k^2 by ring]
      exact Nat.mul_div_right _ (by norm_num)
    have hright : (2*k+1)^2/4=k*(k+1) := by
      rw [show (2*k+1)^2=4*k*(k+1)+1 by ring]
      apply Nat.div_eq_of_lt_le <;> nlinarith
    rw [hleft, hright]
    have hkle : k ≤ k*(k+1) := by nlinarith
    have hs : k*(k+1)-k = k^2 := by
      apply (Nat.sub_eq_iff_eq_add hkle).2
      ring
    exact hs.symm

lemma triangle_nonempty_of_edge_gt_floor
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : (Fintype.card α) ^ 2 / 4 < #G.edgeFinset) :
    (G.cliqueFinset 3).Nonempty := by
  by_contra hn
  have hfree : G.CliqueFree 3 :=
    (SimpleGraph.cliqueFinset_eq_empty_iff.mp
      (Finset.not_nonempty_iff_eq_empty.mp hn))
  have hbound := hfree.card_edgeFinset_le
  norm_num at hbound
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card α) with hmod | hmod
  · simp [hmod] at hbound
    omega
  · simp [hmod] at hbound
    omega

lemma triangle_nonempty_of_edge_gt
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : ((Fintype.card α) ^ 2 - (Fintype.card α % 2) ^ 2) / 4 +
      (Fintype.card α % 2).choose 2 < #G.edgeFinset) :
    (G.cliqueFinset 3).Nonempty := by
  by_contra hn
  have hfree : G.CliqueFree 3 :=
    (SimpleGraph.cliqueFinset_eq_empty_iff.mp (Finset.not_nonempty_iff_eq_empty.mp hn))
  have hbound := hfree.card_edgeFinset_le
  norm_num at hbound
  omega

lemma card_induce_compl_singleton
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    #(G.induce ({v}ᶜ : Set α)).edgeFinset =
      #G.edgeFinset - G.degree v := by
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

lemma triangle_count_induce_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Set α) [Fintype ↥s] :
    #((G.induce s).cliqueFinset 3) ≤ #(G.cliqueFinset 3) := by
  let f : ↥s ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (G.induce s).map f ≤ G := by
    intro a b hab
    rcases (SimpleGraph.map_adj f (G.induce s) a b).1 hab with ⟨a', b', hab', rfl, rfl⟩
    exact hab'
  have hcard : #(((G.induce s).map f).cliqueFinset 3) =
      #((G.induce s).cliqueFinset 3) := by
    rw [SimpleGraph.cliqueFinset_map (G.induce s) f (by decide)]
    simp
  rw [← hcard]
  exact Finset.card_le_card (SimpleGraph.cliqueFinset_mono G hmap)

def remaining {α : Type*} [Fintype α] [DecidableEq α] (a b : α) : Finset α :=
  (Finset.univ.erase a).erase b

lemma edge_sdiff_filter_subset_incidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (a b : α) :
    G.edgeFinset \ {e ∈ G.edgeFinset | e.toFinset ⊆ remaining a b} ⊆
      G.incidenceFinset a ∪ G.incidenceFinset b := by
  intro e
  refine Sym2.inductionOn e ?_
  intro u v he
  have he' := Finset.mem_sdiff.mp he
  simp only [Finset.mem_union, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.mk'_mem_incidenceSet_iff]
  by_contra h
  push_neg at h
  apply he'.2
  apply Finset.mem_filter.mpr
  refine ⟨he'.1, ?_⟩
  intro x hx
  simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hx
  simp only [remaining, Finset.mem_erase, Finset.mem_univ, true_and]
  aesop

lemma incidence_inter_of_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {a b : α} (hab : G.Adj a b) (hne : a ≠ b) :
    G.incidenceFinset a ∩ G.incidenceFinset b = {s(a, b)} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  simp only [Finset.mem_inter, Finset.mem_singleton,
    SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff,
    Sym2.eq_iff]
  constructor <;> aesop (add simp [Sym2.eq_iff, SimpleGraph.adj_comm])

lemma card_filter_remaining_ge
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {a b : α} (hab : G.Adj a b) (hne : a ≠ b) :
    #({e ∈ G.edgeFinset | e.toFinset ⊆ remaining a b}) ≥
      #G.edgeFinset - (G.degree a + G.degree b - 1) := by
  let t : Finset (Sym2 α) := {e ∈ G.edgeFinset | e.toFinset ⊆ remaining a b}
  have ht : t ⊆ G.edgeFinset := Finset.filter_subset _ _
  have hdiff : #(G.edgeFinset \ t) = #G.edgeFinset - #t :=
    Finset.card_sdiff_of_subset ht
  have hsub : G.edgeFinset \ t ⊆ G.incidenceFinset a ∪ G.incidenceFinset b := by
    simpa [t] using edge_sdiff_filter_subset_incidence G a b
  have hle : #(G.edgeFinset \ t) ≤
      #(G.incidenceFinset a ∪ G.incidenceFinset b) :=
    Finset.card_le_card hsub
  have hunion : #(G.incidenceFinset a ∪ G.incidenceFinset b) =
      G.degree a + G.degree b - 1 := by
    rw [Finset.card_union, incidence_inter_of_adj G hab hne]
    simp
  rw [hdiff, hunion] at hle
  dsimp [t] at hle ⊢
  omega

lemma pair_inter_card_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B C : Finset α) :
    #A + #B + #C ≤ Fintype.card α + #(A ∩ B) + #(A ∩ C) + #(B ∩ C) := by
  let f : α → ℕ := fun x =>
    (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) +
      (if x ∈ C then 1 else 0)
  let g : α → ℕ := fun x =>
    1 + (if x ∈ A ∩ B then 1 else 0) +
      (if x ∈ A ∩ C then 1 else 0) + (if x ∈ B ∩ C then 1 else 0)
  have hpoint : ∀ x ∈ (Finset.univ : Finset α), f x ≤ g x := by
    intro x hx
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;>
      simp [f, g, hA, hB, hC]
  have hsum := Finset.sum_le_sum hpoint
  have hA : (∑ x ∈ (Finset.univ : Finset α), if x ∈ A then 1 else 0) = #A := by
    rw [← Finset.card_filter]
    simp
  have hB : (∑ x ∈ (Finset.univ : Finset α), if x ∈ B then 1 else 0) = #B := by
    rw [← Finset.card_filter]
    simp
  have hC : (∑ x ∈ (Finset.univ : Finset α), if x ∈ C then 1 else 0) = #C := by
    rw [← Finset.card_filter]
    simp
  have hAB : (∑ x ∈ (Finset.univ : Finset α), if x ∈ A ∩ B then 1 else 0) =
      #(A ∩ B) := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  have hAC : (∑ x ∈ (Finset.univ : Finset α), if x ∈ A ∩ C then 1 else 0) =
      #(A ∩ C) := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  have hBC : (∑ x ∈ (Finset.univ : Finset α), if x ∈ B ∩ C then 1 else 0) =
      #(B ∩ C) := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  dsimp [f, g] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC, hAB, hAC, hBC,
    Finset.sum_const] at hsum
  simpa [Finset.card_univ] using hsum

def outside3 {α : Type*} [Fintype α] [DecidableEq α]
    (a b c : α) : Finset α :=
  ((Finset.univ.erase a).erase b).erase c

lemma card_pair_filter_ge_of_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B R : Finset α) (d : α)
    (hout : ∀ x ∈ A ∩ B, x ∉ R → x = d) :
    #(A ∩ B) ≤ #((A ∩ B).filter (fun x => x ∈ R)) + 1 := by
  have hsub : A ∩ B ⊆
      (A ∩ B).filter (fun x => x ∈ R) ∪ {d} := by
    intro x hx
    by_cases hR : x ∈ R
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hx, hR⟩))
    · apply Finset.mem_union.mpr (Or.inr ?_)
      simp only [Finset.mem_singleton]
      exact hout x hx hR
  have hcard := Finset.card_le_card hsub
  have hu : #((A ∩ B).filter (fun x => x ∈ R) ∪ {d}) ≤
      #((A ∩ B).filter (fun x => x ∈ R)) + 1 := by
    calc
      #((A ∩ B).filter (fun x => x ∈ R) ∪ {d}) ≤
          #((A ∩ B).filter (fun x => x ∈ R)) + #{d} :=
        Finset.card_union_le _ _
      _ ≤ #((A ∩ B).filter (fun x => x ∈ R)) + 1 := by simp
  exact hcard.trans hu

lemma card_pair_filter_outside3_ge
    {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A B : Finset α)
    (hA : ∀ x ∈ A, x ≠ a) (hB : ∀ x ∈ B, x ≠ b) :
    #(A ∩ B) ≤ #((A ∩ B).filter (fun x => x ∈ outside3 a b c)) + 1 := by
  have hsub : A ∩ B ⊆
      (A ∩ B).filter (fun x => x ∈ outside3 a b c) ∪ {c} := by
    intro x hx
    by_cases hR : x ∈ outside3 a b c
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hx, hR⟩))
    · apply Finset.mem_union.mpr (Or.inr ?_)
      simp only [Finset.mem_singleton]
      have hx' := Finset.mem_inter.mp hx
      have hxa := hA x hx'.1
      have hxb := hB x hx'.2
      simp only [outside3, Finset.mem_erase, Finset.mem_univ, true_and] at hR
      aesop
  have hcard := Finset.card_le_card hsub
  have hu : #((A ∩ B).filter (fun x => x ∈ outside3 a b c) ∪ {c}) ≤
      #((A ∩ B).filter (fun x => x ∈ outside3 a b c)) + 1 := by
    calc
      #((A ∩ B).filter (fun x => x ∈ outside3 a b c) ∪ {c}) ≤
          #((A ∩ B).filter (fun x => x ∈ outside3 a b c)) + #{c} :=
        Finset.card_union_le _ _
      _ ≤ #((A ∩ B).filter (fun x => x ∈ outside3 a b c)) + 1 := by simp
  exact hcard.trans hu

lemma card_image_triple_of_not_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) (A : Finset α)
    (hA : ∀ x ∈ A, x ≠ a) (hB : ∀ x ∈ A, x ≠ b) :
    #(A.image (fun x => ({a, b, x} : Finset α))) = #A := by
  rw [Finset.card_image_iff]
  intro x hx y hy hxy
  have hxmem : x ∈ ({a, b, x} : Finset α) := by simp
  change ({a, b, x} : Finset α) = {a, b, y} at hxy
  have hxmem' : x ∈ ({a, b, y} : Finset α) := by
    rw [← hxy]
    exact hxmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem'
  have hxa := hA x hx
  have hxb := hB x hx
  aesop

lemma triple_images_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q r : α} (hpq : p ≠ q) (hqr : q ≠ r)
    (R I J : Finset α)
    (hI : ∀ x ∈ I, x ∈ R) (hJ : ∀ x ∈ J, x ∈ R)
    (hqR : ∀ x ∈ R, x ≠ q) :
    Disjoint (I.image (fun x => ({p, q, x} : Finset α)))
      (J.image (fun x => ({p, r, x} : Finset α))) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  rcases Finset.mem_image.mp hs with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hs' with ⟨y, hy, hEq⟩
  have hqmem : q ∈ ({p, q, x} : Finset α) := by simp
  have hqmem' : q ∈ ({p, r, y} : Finset α) := by
    rw [hEq]
    exact hqmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem'
  have hqR' := hqR y (hJ y hy)
  aesop

lemma card_outside3
    {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #(outside3 a b c) = Fintype.card α - 3 := by
  rw [outside3]
  have hb : b ∈ Finset.univ.erase a := by simp [Ne.symm hab]
  have hc : c ∈ (Finset.univ.erase a).erase b := by
    simp [Ne.symm hac, Ne.symm hbc]
  rw [Finset.card_erase_of_mem hc, Finset.card_erase_of_mem hb,
    Finset.card_erase_of_mem (Finset.mem_univ a)]
  have hnot : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
  have htriple : #({a, b, c} : Finset α) = 3 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_pair hbc]
  have hthree : 3 ≤ Fintype.card α := by
    have hsub : ({a, b, c} : Finset α) ⊆ Finset.univ := by simp
    have hcard := Finset.card_le_card hsub
    rw [htriple, Finset.card_univ] at hcard
    exact hcard
  rw [Finset.card_univ]
  omega

lemma degree_le_filter_outside3_add_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.degree a ≤ #((outside3 a b c).filter (G.Adj a)) + 2 := by
  have hsub : G.neighborFinset a ⊆
      (outside3 a b c).filter (G.Adj a) ∪ {b, c} := by
    intro x hx
    have hax : G.Adj a x := (G.mem_neighborFinset a x).mp hx
    have hxa : x ≠ a := (G.ne_of_adj hax).symm
    by_cases hR : x ∈ outside3 a b c
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hR, hax⟩))
    · apply Finset.mem_union.mpr (Or.inr ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hxb : x = b
      · exact Or.inl hxb
      · right
        by_contra hxc
        apply hR
        simp [outside3, hxa, hxb, hxc]
  have hcard := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hpair : #({b, c} : Finset α) ≤ 2 := by
    by_cases h : b = c
    · subst c
      simp
    · rw [Finset.card_pair h]
  have hunion : #((outside3 a b c).filter (G.Adj a) ∪ {b, c}) ≤
      #((outside3 a b c).filter (G.Adj a)) + 2 := by
    calc
      #((outside3 a b c).filter (G.Adj a) ∪ {b, c}) ≤
          #((outside3 a b c).filter (G.Adj a)) + #{b, c} :=
        Finset.card_union_le _ _
      _ ≤ #((outside3 a b c).filter (G.Adj a)) + 2 :=
        Nat.add_le_add_left hpair _
  exact hcard.trans hunion

lemma triangle_count_induce_add_one_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Set α) [Fintype ↥s] (v : α) (hv : v ∉ s)
    {t : Finset α} (ht : t ∈ G.cliqueFinset 3) (hvt : v ∈ t) :
    #((G.induce s).cliqueFinset 3) + 1 ≤ #(G.cliqueFinset 3) := by
  let f : ↥s ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (G.induce s).map f ≤ G := by
    intro x y hxy
    rcases (SimpleGraph.map_adj f (G.induce s) x y).1 hxy with
      ⟨x', y', hxy', rfl, rfl⟩
    exact hxy'
  let φ : Finset ↥s ↪ Finset α :=
    ⟨Finset.map f, Finset.map_injective f⟩
  let T : Finset (Finset α) := (G.induce s).cliqueFinset 3 |>.map φ
  have hTcard : #T = #((G.induce s).cliqueFinset 3) := by
    simp [T, φ]
  have hTsub : T ⊆ G.cliqueFinset 3 := by
    intro q hq
    rcases Finset.mem_map.mp hq with ⟨r, hr, rfl⟩
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    exact (SimpleGraph.IsNClique.mono hmap (SimpleGraph.IsNClique.map
      (SimpleGraph.mem_cliqueFinset_iff.mp hr)))
  have ht_not : t ∉ T := by
    intro htm
    rcases Finset.mem_map.mp htm with ⟨r, hr, hEq⟩
    have hvmap : v ∈ Finset.map f r := by
      change v ∈ φ r
      rw [hEq]
      exact hvt
    rcases Finset.mem_map.mp hvmap with ⟨x, hx, hfx⟩
    have hxnot : (x : α) ≠ v := by
      intro hxv
      apply hv
      exact hxv ▸ x.property
    apply hxnot
    simpa [f] using hfx
  have hsub : T ∪ {t} ⊆ G.cliqueFinset 3 := by
    exact Finset.union_subset hTsub (Finset.singleton_subset_iff.mpr ht)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr ht_not),
    hTcard] at hcard
  simpa using hcard

lemma triangle_count_ge_degree_sum_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {a b c : α}
    (habG : G.Adj a b) (hacG : G.Adj a c) (hbcG : G.Adj b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.degree a + G.degree b + G.degree c - Fintype.card α - 2 ≤
      #(G.cliqueFinset 3) := by
  let A : Finset α := G.neighborFinset a
  let B : Finset α := G.neighborFinset b
  let C : Finset α := G.neighborFinset c
  let R : Finset α := outside3 a b c
  have hA : ∀ x ∈ A, x ≠ a := by
    intro x hx
    exact (G.ne_of_adj ((G.mem_neighborFinset a x).mp (by simpa [A] using hx))).symm
  have hB : ∀ x ∈ B, x ≠ b := by
    intro x hx
    exact (G.ne_of_adj ((G.mem_neighborFinset b x).mp (by simpa [B] using hx))).symm
  have hC : ∀ x ∈ C, x ≠ c := by
    intro x hx
    exact (G.ne_of_adj ((G.mem_neighborFinset c x).mp (by simpa [C] using hx))).symm
  have hR_a : ∀ x ∈ R, x ≠ a := by
    intro x hx hxa
    subst x
    simpa [R, outside3] using hx
  have hR_b : ∀ x ∈ R, x ≠ b := by
    intro x hx hxb
    subst x
    simpa [R, outside3] using hx
  have hR_c : ∀ x ∈ R, x ≠ c := by
    intro x hx hxc
    subst x
    simpa [R, outside3] using hx
  have hout_ab : ∀ x ∈ A ∩ B, x ∉ R → x = c := by
    intro x hx hnot
    have hx' := Finset.mem_inter.mp hx
    have hxa := hA x hx'.1
    have hxb := hB x hx'.2
    by_contra hxc
    apply hnot
    simp [R, outside3, hxa, hxb, hxc]
  have hout_ac : ∀ x ∈ A ∩ C, x ∉ R → x = b := by
    intro x hx hnot
    have hx' := Finset.mem_inter.mp hx
    have hxa := hA x hx'.1
    have hxc := hC x hx'.2
    by_contra hxb
    apply hnot
    simp [R, outside3, hxa, hxb, hxc]
  have hout_bc : ∀ x ∈ B ∩ C, x ∉ R → x = a := by
    intro x hx hnot
    have hx' := Finset.mem_inter.mp hx
    have hxb := hB x hx'.1
    have hxc := hC x hx'.2
    by_contra hxa
    apply hnot
    simp [R, outside3, hxa, hxb, hxc]
  let Iab : Finset α := (A ∩ B).filter (fun x => x ∈ R)
  let Iac : Finset α := (A ∩ C).filter (fun x => x ∈ R)
  let Ibc : Finset α := (B ∩ C).filter (fun x => x ∈ R)
  have hiab : #(A ∩ B) ≤ #Iab + 1 := by
    simpa [Iab] using card_pair_filter_ge_of_compl A B R c hout_ab
  have hiac : #(A ∩ C) ≤ #Iac + 1 := by
    simpa [Iac] using card_pair_filter_ge_of_compl A C R b hout_ac
  have hibc : #(B ∩ C) ≤ #Ibc + 1 := by
    simpa [Ibc] using card_pair_filter_ge_of_compl B C R a hout_bc
  let Uab : Finset (Finset α) := Iab.image (fun x => ({a, b, x} : Finset α))
  let Uac : Finset (Finset α) := Iac.image (fun x => ({a, c, x} : Finset α))
  let Ubc : Finset (Finset α) := Ibc.image (fun x => ({b, c, x} : Finset α))
  have huab : #Uab = #Iab := by
    dsimp [Uab]
    apply card_image_triple_of_not_mem hab Iab
    · intro x hx
      apply hA x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    · intro x hx
      apply hB x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have huac : #Uac = #Iac := by
    dsimp [Uac]
    apply card_image_triple_of_not_mem hac Iac
    · intro x hx
      apply hA x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    · intro x hx
      apply hC x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have hubc : #Ubc = #Ibc := by
    dsimp [Ubc]
    apply card_image_triple_of_not_mem hbc Ibc
    · intro x hx
      apply hB x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    · intro x hx
      apply hC x
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have hUab : Uab ⊆ G.cliqueFinset 3 := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, rfl⟩
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    apply SimpleGraph.is3Clique_triple_iff.mpr
    have hx' := Finset.mem_filter.mp hx
    have hxx := Finset.mem_inter.mp hx'.1
    exact ⟨habG, (G.mem_neighborFinset a x).mp hxx.1,
      (G.mem_neighborFinset b x).mp hxx.2⟩
  have hUac : Uac ⊆ G.cliqueFinset 3 := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, rfl⟩
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    apply SimpleGraph.is3Clique_triple_iff.mpr
    have hx' := Finset.mem_filter.mp hx
    have hxx := Finset.mem_inter.mp hx'.1
    exact ⟨hacG, (G.mem_neighborFinset a x).mp hxx.1,
      (G.mem_neighborFinset c x).mp hxx.2⟩
  have hUbc : Ubc ⊆ G.cliqueFinset 3 := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, rfl⟩
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    apply SimpleGraph.is3Clique_triple_iff.mpr
    have hx' := Finset.mem_filter.mp hx
    have hxx := Finset.mem_inter.mp hx'.1
    exact ⟨hbcG, (G.mem_neighborFinset b x).mp hxx.1,
      (G.mem_neighborFinset c x).mp hxx.2⟩
  have hd_ab_ac : Disjoint Uab Uac := by
    dsimp [Uab, Uac]
    apply triple_images_disjoint hab hbc R Iab Iac
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · exact hR_b
  have hd_ab_bc : Disjoint Uab Ubc := by
    simpa [Uab, Ubc, Finset.insert_comm] using
      (triple_images_disjoint (p := b) (q := a) (r := c)
        (Ne.symm hab) hac R Iab Ibc
        (by intro x hx; exact (Finset.mem_filter.mp hx).2)
        (by intro x hx; exact (Finset.mem_filter.mp hx).2) hR_a)
  have hd_ac_bc : Disjoint Uac Ubc := by
    simpa [Uac, Ubc, Finset.insert_comm] using
      (triple_images_disjoint (p := c) (q := a) (r := b)
        (Ne.symm hac) hab R Iac Ibc
        (by intro x hx; exact (Finset.mem_filter.mp hx).2)
        (by intro x hx; exact (Finset.mem_filter.mp hx).2) hR_a)
  have hd_union : Disjoint (Uab ∪ Uac) Ubc :=
    Finset.disjoint_union_left.mpr ⟨hd_ab_bc, hd_ac_bc⟩
  have hcardU : #(Uab ∪ Uac ∪ Ubc) = #Uab + #Uac + #Ubc := by
    rw [Finset.card_union_of_disjoint hd_union,
      Finset.card_union_of_disjoint hd_ab_ac]
  have hbase : ({a, b, c} : Finset α) ∈ G.cliqueFinset 3 := by
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨habG, hacG, hbcG⟩
  have hbase_not_ab : ({a, b, c} : Finset α) ∉ Uab := by
    intro hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, hEq⟩
    have hc : c ∈ ({a, b, x} : Finset α) := by
      rw [hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    have hxEq : x = c := by
      rcases hc with h | h | h
      · exact (Ne.symm hac h).elim
      · exact (Ne.symm hbc h).elim
      · exact h.symm
    have hxR := (Finset.mem_filter.mp hx).2
    exact (hR_c x hxR) hxEq
  have hbase_not_ac : ({a, b, c} : Finset α) ∉ Uac := by
    intro hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, hEq⟩
    have hb : b ∈ ({a, c, x} : Finset α) := by
      rw [hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    have hxEq : x = b := by
      rcases hb with h | h | h
      · exact (Ne.symm hab h).elim
      · exact (hbc h).elim
      · exact h.symm
    have hxR := (Finset.mem_filter.mp hx).2
    exact (hR_b x hxR) hxEq
  have hbase_not_bc : ({a, b, c} : Finset α) ∉ Ubc := by
    intro hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, hEq⟩
    have ha : a ∈ ({b, c, x} : Finset α) := by
      rw [hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    have hxEq : x = a := by
      rcases ha with h | h | h
      · exact (hab h).elim
      · exact (hac h).elim
      · exact h.symm
    have hxR := (Finset.mem_filter.mp hx).2
    exact (hR_a x hxR) hxEq
  have hbase_not_union : ({a, b, c} : Finset α) ∉ Uab ∪ Uac ∪ Ubc := by
    intro hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact hbase_not_ab hs
      · exact hbase_not_ac hs
    · exact hbase_not_bc hs
  have hbase_disjoint : Disjoint (Uab ∪ Uac ∪ Ubc) {({a, b, c} : Finset α)} := by
    rw [Finset.disjoint_left]
    intro s hs hsbase
    have hsEq : s = ({a, b, c} : Finset α) := by simpa using hsbase
    subst s
    exact hbase_not_union hs
  have hAllsub : Uab ∪ Uac ∪ Ubc ∪ {({a, b, c} : Finset α)} ⊆
      G.cliqueFinset 3 := by
    exact Finset.union_subset
      (Finset.union_subset (Finset.union_subset hUab hUac) hUbc)
      (Finset.singleton_subset_iff.mpr hbase)
  have hAllcard : #(Uab ∪ Uac ∪ Ubc ∪ {({a, b, c} : Finset α)}) =
      #Uab + #Uac + #Ubc + 1 := by
    rw [Finset.card_union_of_disjoint hbase_disjoint, hcardU]
    simp
  have hUcard : #Uab + #Uac + #Ubc + 1 ≤ #(G.cliqueFinset 3) := by
    rw [← hAllcard]
    exact Finset.card_le_card hAllsub
  have hAcard : #A = G.degree a := by
    dsimp [A]
  have hBcard : #B = G.degree b := by
    dsimp [B]
  have hCcard : #C = G.degree c := by
    dsimp [C]
  have hp := pair_inter_card_bound A B C
  rw [hAcard, hBcard, hCcard] at hp
  rw [huab, huac, hubc] at hUcard
  omega

lemma rademacher_aux (n : ℕ) :
    ∀ (α : Type*) [Fintype α] [DecidableEq α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      Fintype.card α = n →
      n ^ 2 / 4 < #G.edgeFinset →
      n / 2 ≤ #(G.cliqueFinset 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α instF instD G instA hcard hE
    by_cases hnsmall : n ≤ 3
    · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · omega
      · omega
      · have hmax := G.card_edgeFinset_le_card_choose_two
        rw [hcard] at hmax
        norm_num at hmax
        omega
      · have hEcard : (Fintype.card α) ^ 2 / 4 < #G.edgeFinset := by
          simpa [hcard] using hE
        obtain ⟨t, ht⟩ := triangle_nonempty_of_edge_gt_floor G hEcard
        have hpos : 1 ≤ #(G.cliqueFinset 3) :=
          Finset.card_pos.mpr ⟨t, ht⟩
        omega
    · have hn4 : 4 ≤ n := by omega
      have hEcard : (Fintype.card α) ^ 2 / 4 < #G.edgeFinset := by
        simpa [hcard] using hE
      obtain ⟨t, ht⟩ := triangle_nonempty_of_edge_gt_floor G hEcard
      obtain ⟨a, b, c, habG, hacG, hbcG, rfl⟩ :=
        SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp ht)
      have hab : a ≠ b := G.ne_of_adj habG
      have hac : a ≠ c := G.ne_of_adj hacG
      have hbc : b ≠ c := G.ne_of_adj hbcG
      have hdelete : ∀ (v : α), v ∈ ({a, b, c} : Finset α) →
          G.degree v ≤ n / 2 → n / 2 ≤ #(G.cliqueFinset 3) := by
        intro v hvt hd
        have hdcard : G.degree v ≤ Fintype.card α / 2 := by
          simpa [hcard] using hd
        have hkg : Fintype.card α / 2 ≤ (Fintype.card α) ^ 2 / 4 := by
          apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
          have hhalf : Fintype.card α / 2 ≤ Fintype.card α :=
            Nat.div_le_self _ _
          nlinarith
        have hdeg_g : G.degree v ≤ (Fintype.card α) ^ 2 / 4 :=
          hdcard.trans hkg
        have hE' : (n - 1) ^ 2 / 4 <
            #((G.induce ({v}ᶜ : Set α)).edgeFinset) := by
          rw [card_induce_compl_singleton, floor_sq_sub_one, ← hcard]
          exact (Nat.sub_le_sub_left hdcard _).trans_lt
            (Nat.sub_lt_sub_right hdeg_g hEcard)
        have hcard_sub : Fintype.card ↥({v}ᶜ : Set α) = n - 1 := by
          change Fintype.card {x : α // x ≠ v} = n - 1
          have hc := Fintype.card_subtype_compl (fun x : α => x = v)
          rw [hcard] at hc
          simpa using hc
        have hrec := ih (n - 1) (by omega)
          (↥({v}ᶜ : Set α)) (G.induce ({v}ᶜ : Set α)) hcard_sub hE'
        have hadd := triangle_count_induce_add_one_le G ({v}ᶜ : Set α) v
          (by simp) ht hvt
        have hstep : (n - 1) / 2 + 1 ≤ #(G.cliqueFinset 3) :=
          (Nat.add_le_add_right hrec 1).trans hadd
        omega
      by_cases hda : G.degree a ≤ n / 2
      · exact hdelete a (by simp) hda
      by_cases hdb : G.degree b ≤ n / 2
      · exact hdelete b (by simp) hdb
      by_cases hdc : G.degree c ≤ n / 2
      · exact hdelete c (by simp) hdc
      have hbase := triangle_count_ge_degree_sum_sub G habG hacG hbcG hab hac hbc
      rw [hcard] at hbase
      omega

 theorem rademacher_triangle_supersaturation
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : (Fintype.card α) ^ 2 / 4 < #G.edgeFinset) :
    Fintype.card α / 2 ≤ #(G.cliqueFinset 3) := by
  exact rademacher_aux (Fintype.card α) α G rfl h

theorem solution : targetStatement := by
  intro α instF instD G instA h
  exact rademacher_triangle_supersaturation G h

end JSP000840
