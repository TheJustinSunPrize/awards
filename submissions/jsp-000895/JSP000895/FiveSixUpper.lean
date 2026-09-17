/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared with OpenAI Codex assistance.

The mathematical bound is the finite upper bound in Stefan Glock,
"Triple systems with no three triples spanning at most five points",
Section 3, Theorem 8 (arXiv:1809.02100). The supporting bound also appears
in the historical discussion of Erdos Problem 1076.

This module extends the attributed model and deletion lemmas in
JSP000895.FiveThreeUpper. It counts the completed pair shadow: all pairs
in an edge, and all six pairs on the four vertices of an overlapping pair
of distinct edges. F5-freeness separates an edge from an overlapping block;
F6-freeness separates two different overlapping blocks.

Scope: finite simple three-uniform hypergraphs, assuming only FkFree 5
and FkFree 6, with the inherited at-most-k semantics. There is no F4-free
or linearity assumption. This is the finite upper bound, not the matching
lower bound, the full asymptotic, or the entire general-k problem.
-/
import JSP000895.FiveThreeUpper

namespace Erdos1076Upper

open Finset

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Complete the shadow on every overlapping pair of distinct edges. The
additional sixth pair is unused by an F5-free hypergraph, but is part of the
finite ambient pair budget. The condition `A ≠ B` excludes same-edge pseudo-blocks. -/
def completedPairShadow (G : TripleSystemOn V) : Finset (Finset V) :=
  pairShadow G ∪ G.biUnion (fun A ↦ G.biUnion (fun B ↦
    if A ≠ B ∧ (A.1 ∩ B.1).card = 2 then (A.1 ∪ B.1).powersetCard 2 else ∅))

lemma pairShadow_subset_completedPairShadow (G : TripleSystemOn V) :
    pairShadow G ⊆ completedPairShadow G := subset_union_left

lemma blockPairs_subset_completedPairShadow {G : TripleSystemOn V}
    {A B : TripleOn V} (hA : A ∈ G) (hB : B ∈ G)
    (hAB : A ≠ B) (hinter : (A.1 ∩ B.1).card = 2) :
    (A.1 ∪ B.1).powersetCard 2 ⊆ completedPairShadow G := by
  intro p hp
  apply mem_union.mpr
  right
  apply mem_biUnion.mpr
  refine ⟨A, hA, mem_biUnion.mpr ⟨B, hB, ?_⟩⟩
  rw [if_pos (show A ≠ B ∧ (A.1 ∩ B.1).card = 2 from ⟨hAB, hinter⟩)]
  exact hp

lemma pair_or_block_of_mem_completedPairShadow {G : TripleSystemOn V}
    {p : Finset V} (hp : p ∈ completedPairShadow G) :
    p ∈ pairShadow G ∨
      ∃ A ∈ G, ∃ B ∈ G, A ≠ B ∧ (A.1 ∩ B.1).card = 2 ∧
        p ∈ (A.1 ∪ B.1).powersetCard 2 := by
  rcases mem_union.mp hp with hp | hp
  · exact Or.inl hp
  · obtain ⟨A, hA, hp⟩ := mem_biUnion.mp hp
    obtain ⟨B, hB, hp⟩ := mem_biUnion.mp hp
    by_cases hAB : A ≠ B ∧ (A.1 ∩ B.1).card = 2
    · exact Or.inr ⟨A, hA, B, hB, hAB.1, hAB.2, by simpa [hAB] using hp⟩
    · simp [hAB] at hp

lemma completedPairShadow_mono {G H : TripleSystemOn V} (hGH : G ⊆ H) :
    completedPairShadow G ⊆ completedPairShadow H := by
  intro p hp
  rcases pair_or_block_of_mem_completedPairShadow hp with hp | ⟨A, hA, B, hB, hAB, hi, hp⟩
  · apply pairShadow_subset_completedPairShadow
    obtain ⟨A, hA, hp⟩ := mem_biUnion.mp hp
    exact mem_biUnion.mpr ⟨A, hGH hA, hp⟩
  · exact blockPairs_subset_completedPairShadow (hGH hA) (hGH hB) hAB hi hp

lemma shared_pair_of_inter_card_two {A B : TripleOn V}
    (hinter : (A.1 ∩ B.1).card = 2) :
    ∃ p : Finset V, p ∈ edgePairs A ∧ p ∈ edgePairs B := by
  refine ⟨A.1 ∩ B.1, ?_, ?_⟩
  · exact mem_powersetCard.mpr ⟨inter_subset_left, hinter⟩
  · exact mem_powersetCard.mpr ⟨inter_subset_right, hinter⟩

lemma card_blockPairs_eq_six {A B : TripleOn V}
    (hAB : A ≠ B) (hinter : (A.1 ∩ B.1).card = 2) :
    ((A.1 ∪ B.1).powersetCard 2).card = 6 := by
  obtain ⟨p, hpA, hpB⟩ := shared_pair_of_inter_card_two hinter
  rw [card_powersetCard, card_union_eq_four hAB hpA hpB]
  decide

/-- Four distinct edges in an F6-free system span more than six vertices. -/
lemma six_lt_union_four {G : TripleSystemOn V} (hG : FkFree 6 G)
    {A B C D : TripleOn V} (hA : A ∈ G) (hB : B ∈ G)
    (hC : C ∈ G) (hD : D ∈ G)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    6 < ((A.1 ∪ B.1) ∪ (C.1 ∪ D.1)).card := by
  have hsub : ({A, B, C, D} : TripleSystemOn V) ⊆ G := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hA, hB, hC, hD⟩
  have hcard : ({A, B, C, D} : TripleSystemOn V).card = 6 - 2 := by
    simp [hAB, hAC, hAD, hBC, hBD, hCD]
  simpa [verticesOn, union_assoc] using hG {A, B, C, D} hsub hcard

/-- Two edge-disjoint double-edge blocks cannot have a pair in common in
their completed shadows: that would put four distinct edges on at most six
vertices. The six pairwise edge inequalities are explicit. -/
lemma blockPairs_disjoint_of_six_free {G : TripleSystemOn V} (hG : FkFree 6 G)
    {A B C D : TripleOn V} (hA : A ∈ G) (hB : B ∈ G)
    (hC : C ∈ G) (hD : D ∈ G)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hiAB : (A.1 ∩ B.1).card = 2) (hiCD : (C.1 ∩ D.1).card = 2) :
    Disjoint ((A.1 ∪ B.1).powersetCard 2) ((C.1 ∪ D.1).powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro p hpAB hpCD
  obtain ⟨hpAB, hpcard⟩ := mem_powersetCard.mp hpAB
  obtain ⟨hpCD, _⟩ := mem_powersetCard.mp hpCD
  have hlo := card_le_card (subset_inter hpAB hpCD)
  obtain ⟨q, hqA, hqB⟩ := shared_pair_of_inter_card_two hiAB
  obtain ⟨q', hqC, hqD⟩ := shared_pair_of_inter_card_two hiCD
  have hfourAB := card_union_eq_four hAB hqA hqB
  have hfourCD := card_union_eq_four hCD hqC hqD
  have hcount := card_union_add_card_inter (A.1 ∪ B.1) (C.1 ∪ D.1)
  have hlarge := six_lt_union_four hG hA hB hC hD hAB hAC hAD hBC hBD hCD
  rw [hfourAB, hfourCD] at hcount
  omega

/-- A single edge needs three pairs; a double-edge block needs six. The
completed shadow supplies these disjoint resources using only F5 and F6. -/
theorem three_mul_card_le_completedPairShadow (G : TripleSystemOn V)
    (h5 : FkFree 5 G) (h6 : FkFree 6 G) :
    3 * G.card ≤ (completedPairShadow G).card := by
  classical
  revert h5 h6
  induction G using Finset.strongInductionOn with
  | _ G ih =>
    intro h5 h6
    by_cases hempty : G = ∅
    · subst G
      simp
    obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    by_cases hpartner : ∃ B ∈ G, B ≠ A ∧
        ∃ p : Finset V, p ∈ edgePairs A ∧ p ∈ edgePairs B
    · obtain ⟨B, hB, hBA, p, hpA, hpB⟩ := hpartner
      let R : TripleSystemOn V := (G.erase A).erase B
      have hRG : R ⊆ G := by
        intro C hC
        exact (mem_erase.mp (mem_erase.mp hC).2).2
      have hRlt : R ⊂ G := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hRG, ?_⟩
        intro heq
        have hAR : A ∈ R := heq.symm ▸ hA
        exact (notMem_erase A G) (mem_erase.mp hAR).2
      have hR := ih R hRlt (h5.mono hRG) (h6.mono hRG)
      have hB' : B ∈ G.erase A := mem_erase.mpr ⟨hBA, hB⟩
      have hcardA := card_erase_add_one hA
      have hcardB := card_erase_add_one hB'
      have hcardR : R.card + 2 = G.card := by
        dsimp [R]
        omega
      have hiAB : (A.1 ∩ B.1).card = 2 := card_inter_eq_two hBA.symm hpA hpB
      have hdis : Disjoint ((A.1 ∪ B.1).powersetCard 2) (completedPairShadow R) := by
        rw [Finset.disjoint_left]
        intro q hq hqR
        rcases pair_or_block_of_mem_completedPairShadow hqR with hqR |
            ⟨C, hCR, D, hDR, hCD, hiCD, hqCD⟩
        · obtain ⟨C, hCR, hqC⟩ := mem_biUnion.mp hqR
          have hCA : C ≠ A := (mem_erase.mp (mem_erase.mp hCR).2).1
          have hCB : C ≠ B := (mem_erase.mp hCR).1
          exact no_third_pair h5 hA hB (hRG hCR) hBA.symm hCA.symm hCB.symm
            hpA hpB (mem_powersetCard.mp hq).1 hqC
        · have hCA : C ≠ A := (mem_erase.mp (mem_erase.mp hCR).2).1
          have hCB : C ≠ B := (mem_erase.mp hCR).1
          have hDA : D ≠ A := (mem_erase.mp (mem_erase.mp hDR).2).1
          have hDB : D ≠ B := (mem_erase.mp hDR).1
          exact Finset.disjoint_left.mp
            (blockPairs_disjoint_of_six_free h6 hA hB (hRG hCR) (hRG hDR)
              hBA.symm hCA.symm hDA.symm hCB.symm hDB.symm hCD hiAB hiCD) hq hqCD
      have hsub : (A.1 ∪ B.1).powersetCard 2 ∪ completedPairShadow R ⊆
          completedPairShadow G :=
        union_subset (blockPairs_subset_completedPairShadow hA hB hBA.symm hiAB)
          (completedPairShadow_mono hRG)
      have hcount := card_le_card hsub
      rw [card_union_of_disjoint hdis, card_blockPairs_eq_six hBA.symm hiAB] at hcount
      omega
    · have hRG : G.erase A ⊆ G := erase_subset A G
      have hR := ih (G.erase A) (erase_ssubset hA) (h5.mono hRG) (h6.mono hRG)
      have hcard := card_erase_add_one hA
      have hdis : Disjoint (edgePairs A) (completedPairShadow (G.erase A)) := by
        rw [Finset.disjoint_left]
        intro q hqA hqR
        rcases pair_or_block_of_mem_completedPairShadow hqR with hqR |
            ⟨C, hCR, D, hDR, hCD, hiCD, hqCD⟩
        · obtain ⟨B, hBR, hqB⟩ := mem_biUnion.mp hqR
          exact hpartner ⟨B, (mem_erase.mp hBR).2,
            (mem_erase.mp hBR).1, q, hqA, hqB⟩
        · have hCA : C ≠ A := (mem_erase.mp hCR).1
          have hDA : D ≠ A := (mem_erase.mp hDR).1
          obtain ⟨p, hpC, hpD⟩ := shared_pair_of_inter_card_two hiCD
          exact no_third_pair h5 (hRG hCR) (hRG hDR) hA hCD hCA hDA
            hpC hpD (mem_powersetCard.mp hqCD).1 hqA
      have hsubA : edgePairs A ⊆ completedPairShadow G := by
        intro q hq
        exact pairShadow_subset_completedPairShadow G (mem_biUnion.mpr ⟨A, hA, hq⟩)
      have hsub : edgePairs A ∪ completedPairShadow (G.erase A) ⊆ completedPairShadow G :=
        union_subset hsubA (completedPairShadow_mono hRG)
      have hcount := card_le_card hsub
      rw [card_union_of_disjoint hdis, card_edgePairs] at hcount
      omega

/-- Glock's finite F5-and-F6 upper bound. F4-freeness and linearity are not
assumed. The inherited at-most-k convention makes the statement valid for
all natural ambient orders, including those smaller than six. -/
theorem three_mul_card_le_choose_of_five_six {n : ℕ} (G : TripleSystem n)
    (h5 : FkFree 5 G) (h6 : FkFree 6 G) : 3 * G.card ≤ n.choose 2 := by
  classical
  have hsub : completedPairShadow G ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro p hp
    have hpcard : p.card = 2 := by
      rcases pair_or_block_of_mem_completedPairShadow hp with hp |
          ⟨A, hA, B, hB, hAB, hinter, hp⟩
      · obtain ⟨A, hA, hp⟩ := mem_biUnion.mp hp
        exact (mem_powersetCard.mp hp).2
      · exact (mem_powersetCard.mp hp).2
    exact mem_powersetCard.mpr ⟨subset_univ _, hpcard⟩
  have hcard := card_le_card hsub
  simp only [card_powersetCard, card_univ, Fintype.card_fin] at hcard
  exact (three_mul_card_le_completedPairShadow G h5 h6).trans hcard

/-- The supporting theorem in the problem's historical discussion, in the
same at-most-k convention: exceeding the pair budget forces one of the two
forbidden families. The upper bound itself is non-strict. -/
theorem not_five_free_or_not_six_free_of_choose_lt_three_mul_card
    {n : ℕ} (G : TripleSystem n) (hlarge : n.choose 2 < 3 * G.card) :
    ¬FkFree 5 G ∨ ¬FkFree 6 G := by
  by_cases h5 : FkFree 5 G
  · right
    intro h6
    exact (not_lt_of_ge (three_mul_card_le_choose_of_five_six G h5 h6)) hlarge
  · exact Or.inl h5

#print axioms three_mul_card_le_completedPairShadow
#print axioms three_mul_card_le_choose_of_five_six
#print axioms not_five_free_or_not_six_free_of_choose_lt_three_mul_card

end

end Erdos1076Upper
