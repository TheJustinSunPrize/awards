/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared with OpenAI Codex assistance.

The mathematical upper bound is due to Stefan Glock, "Triple systems with
no three triples spanning at most five points", Bull. Lond. Math. Soc. 51
(2019), 230--236, Lemma 4 (arXiv:1809.02100, Section 2.1).

The minimal definitions TripleOn, TripleSystemOn, TripleSystem, verticesOn,
FkFree and extremalNumber below are reproduced, in a separate namespace,
from plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos1076.lean, lines 58--86 (Apache 2.0;
copyright Boris Alexeev, formal authors Codex and GPT-5.6 Sol).
The upper-bound proofs below are a new implementation using deletion of
one edge or a pair of edges and counting the two-element shadow.

Scope: finite simple three-uniform hypergraphs, forbidding any three
distinct edges whose vertex union has at most five vertices. No linearity
assumption is imposed. This is the upper half of the k=5 extremal result,
not a matching lower bound or the entire general-k problem.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Erdos1076Upper

open Finset

noncomputable section

/-- A triple on a finite vertex type. -/
abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

/-- A finite simple three-uniform hypergraph. -/
abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

def verticesOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun e ↦ e.1

/-- At-most-k vertex semantics, including when the ambient order is below k.
For ambient order at least k this is the usual non-induced forbidden family
on exactly k vertices, allowing isolated vertices to be added. -/
def FkFree {V : Type*} [DecidableEq V] (k : ℕ)
    (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 →
    k < (verticesOn C).card

noncomputable def extremalNumber (k n : ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
    if FkFree k G then G.card else 0

variable {V : Type*} [DecidableEq V]

/-- The three unordered pairs contained in a triple. -/
def edgePairs (A : TripleOn V) : Finset (Finset V) := A.1.powersetCard 2

/-- The two-element shadow: every pair used by at least one edge. -/
def pairShadow (G : TripleSystemOn V) : Finset (Finset V) :=
  G.biUnion edgePairs

@[simp] lemma card_edgePairs (A : TripleOn V) : (edgePairs A).card = 3 := by
  simp [edgePairs, A.2]

@[simp] lemma pairShadow_insert (A : TripleOn V) (G : TripleSystemOn V) :
    pairShadow (insert A G) = edgePairs A ∪ pairShadow G := by
  simp [pairShadow]

lemma FkFree.mono {k : ℕ} {G H : TripleSystemOn V}
    (hG : FkFree k G) (hHG : H ⊆ G) : FkFree k H := by
  intro C hC hcard
  exact hG C (hC.trans hHG) hcard

/-- Three distinct edges have a vertex union larger than five. -/
lemma five_lt_union_three {G : TripleSystemOn V} (hG : FkFree 5 G)
    {A B C : TripleOn V} (hA : A ∈ G) (hB : B ∈ G) (hC : C ∈ G)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    5 < ((A.1 ∪ B.1) ∪ C.1).card := by
  have hsub : ({A, B, C} : TripleSystemOn V) ⊆ G := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hA, hB, hC⟩
  have hcard : ({A, B, C} : TripleSystemOn V).card = 5 - 2 := by
    simp [hAB, hAC, hBC]
  simpa [verticesOn, union_assoc] using hG {A, B, C} hsub hcard

lemma shared_pair_subset_inter {A B : TripleOn V} {p : Finset V}
    (hpA : p ∈ edgePairs A) (hpB : p ∈ edgePairs B) :
    p ⊆ A.1 ∩ B.1 ∧ p.card = 2 := by
  obtain ⟨hpA', hcard⟩ := mem_powersetCard.mp hpA
  obtain ⟨hpB', _⟩ := mem_powersetCard.mp hpB
  exact ⟨subset_inter hpA' hpB', hcard⟩

/-- Distinct triples sharing a pair intersect in exactly that pair. -/
lemma card_inter_eq_two {A B : TripleOn V} (hAB : A ≠ B) {p : Finset V}
    (hpA : p ∈ edgePairs A) (hpB : p ∈ edgePairs B) :
    (A.1 ∩ B.1).card = 2 := by
  obtain ⟨hp, hpcard⟩ := shared_pair_subset_inter hpA hpB
  have hlo := card_le_card hp
  have hlt : (A.1 ∩ B.1).card < 3 := by
    by_contra hnot
    have hia : A.1 ∩ B.1 = A.1 :=
      eq_of_subset_of_card_le inter_subset_left (by rw [A.2]; omega)
    have hib : A.1 ∩ B.1 = B.1 :=
      eq_of_subset_of_card_le inter_subset_right (by rw [B.2]; omega)
    exact hAB (Subtype.ext (hia.symm.trans hib))
  omega

lemma card_union_eq_four {A B : TripleOn V} (hAB : A ≠ B) {p : Finset V}
    (hpA : p ∈ edgePairs A) (hpB : p ∈ edgePairs B) :
    (A.1 ∪ B.1).card = 4 := by
  have h := card_union_add_card_inter A.1 B.1
  rw [A.2, B.2, card_inter_eq_two hAB hpA hpB] at h
  omega

lemma edgePairs_inter (A B : TripleOn V) :
    edgePairs A ∩ edgePairs B = (A.1 ∩ B.1).powersetCard 2 := by
  ext q
  simp only [mem_inter, edgePairs, mem_powersetCard]
  constructor
  · rintro ⟨⟨hA, hcard⟩, hB, _⟩
    exact ⟨subset_inter hA hB, hcard⟩
  · rintro ⟨h, hcard⟩
    exact ⟨⟨h.trans inter_subset_left, hcard⟩,
      ⟨h.trans inter_subset_right, hcard⟩⟩

/-- A pair of distinct overlapping triples uses five different pairs. -/
lemma card_edgePairs_union_eq_five {A B : TripleOn V} (hAB : A ≠ B)
    {p : Finset V} (hpA : p ∈ edgePairs A) (hpB : p ∈ edgePairs B) :
    (edgePairs A ∪ edgePairs B).card = 5 := by
  have h := card_union_add_card_inter (edgePairs A) (edgePairs B)
  rw [card_edgePairs, card_edgePairs, edgePairs_inter, card_powersetCard,
    card_inter_eq_two hAB hpA hpB] at h
  norm_num at h
  omega

/-- No third edge can use a pair inside the four vertices of two edges
sharing a pair. Such an edge would make a forbidden three-edge family. -/
lemma no_third_pair {G : TripleSystemOn V} (hG : FkFree 5 G)
    {A B C : TripleOn V} (hA : A ∈ G) (hB : B ∈ G) (hC : C ∈ G)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {p q : Finset V} (hpA : p ∈ edgePairs A) (hpB : p ∈ edgePairs B)
    (hq : q ⊆ A.1 ∪ B.1) (hqC : q ∈ edgePairs C) : False := by
  obtain ⟨hqC', hqcard⟩ := mem_powersetCard.mp hqC
  have hqinter : q ⊆ (A.1 ∪ B.1) ∩ C.1 := subset_inter hq hqC'
  have htwo := card_le_card hqinter
  have hcount := card_union_add_card_inter (A.1 ∪ B.1) C.1
  have hfour := card_union_eq_four hAB hpA hpB
  have hlarge := five_lt_union_three hG hA hB hC hAB hAC hBC
  rw [C.2, hfour] at hcount
  omega

/-- The key finite inequality. A lone edge uses three private pairs;
a double-edge component uses five. No theorem-bearing hypothesis other
than the actual forbidden configuration is assumed. -/
theorem five_mul_card_le_two_shadow (G : TripleSystemOn V)
    (hG : FkFree 5 G) : 5 * G.card ≤ 2 * (pairShadow G).card := by
  classical
  revert hG
  induction G using Finset.strongInductionOn with
  | _ G ih =>
    intro hG
    by_cases hempty : G = ∅
    · subst G
      simp [pairShadow]
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
      have hR := ih R hRlt (hG.mono hRG)
      have hB' : B ∈ G.erase A := mem_erase.mpr ⟨hBA, hB⟩
      have hcardA := card_erase_add_one hA
      have hcardB := card_erase_add_one hB'
      have hcardR : R.card + 2 = G.card := by
        dsimp [R]
        omega
      have hdecomp : insert A (insert B R) = G := by
        calc
          insert A (insert B R) = insert A (G.erase A) :=
            congrArg (insert A) (insert_erase hB')
          _ = G := insert_erase hA
      have hshadow : pairShadow G =
          (edgePairs A ∪ edgePairs B) ∪ pairShadow R := by
        calc
          pairShadow G = pairShadow (insert A (insert B R)) :=
            congrArg pairShadow hdecomp.symm
          _ = (edgePairs A ∪ edgePairs B) ∪ pairShadow R := by
            simp only [pairShadow_insert, union_assoc]
      have hdis : Disjoint (edgePairs A ∪ edgePairs B) (pairShadow R) := by
        rw [Finset.disjoint_left]
        intro q hq hqR
        obtain ⟨C, hCR, hqC⟩ := mem_biUnion.mp hqR
        have hCG : C ∈ G := hRG hCR
        have hCA : C ≠ A := (mem_erase.mp (mem_erase.mp hCR).2).1
        have hCB : C ≠ B := (mem_erase.mp hCR).1
        have hqsub : q ⊆ A.1 ∪ B.1 := by
          rcases mem_union.mp hq with hqA | hqB
          · exact (mem_powersetCard.mp hqA).1.trans subset_union_left
          · exact (mem_powersetCard.mp hqB).1.trans subset_union_right
        exact no_third_pair hG hA hB hCG hBA.symm hCA.symm hCB.symm
          hpA hpB hqsub hqC
      have hfive := card_edgePairs_union_eq_five hBA.symm hpA hpB
      rw [hshadow, card_union_of_disjoint hdis, hfive]
      omega
    · have hR := ih (G.erase A) (erase_ssubset hA)
          (hG.mono (erase_subset A G))
      have hcard := card_erase_add_one hA
      have hshadow : pairShadow G = edgePairs A ∪ pairShadow (G.erase A) := by
        calc
          pairShadow G = pairShadow (insert A (G.erase A)) :=
            congrArg pairShadow (insert_erase hA).symm
          _ = edgePairs A ∪ pairShadow (G.erase A) := pairShadow_insert A _
      have hdis : Disjoint (edgePairs A) (pairShadow (G.erase A)) := by
        rw [Finset.disjoint_left]
        intro p hpA hpR
        obtain ⟨B, hBR, hpB⟩ := mem_biUnion.mp hpR
        exact hpartner ⟨B, (mem_erase.mp hBR).2,
          (mem_erase.mp hBR).1, p, hpA, hpB⟩
      rw [hshadow, card_union_of_disjoint hdis, card_edgePairs]
      omega

/-- Glock's finite upper bound under the single F5-free hypothesis.
The statement uses at-most-five semantics for every n, including n < 5. -/
theorem five_mul_card_le_two_choose {n : ℕ} (G : TripleSystem n)
    (hG : FkFree 5 G) : 5 * G.card ≤ 2 * n.choose 2 := by
  classical
  have hsub : pairShadow G ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro p hp
    obtain ⟨A, _hA, hpA⟩ := mem_biUnion.mp hp
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_powersetCard.mp hpA).2⟩
  have hcard := card_le_card hsub
  simp only [card_powersetCard, card_univ, Fintype.card_fin] at hcard
  exact (five_mul_card_le_two_shadow G hG).trans (Nat.mul_le_mul_left 2 hcard)

/-- The same finite upper bound for the literal extremal function, whose
definitions agree with the pinned upstream model. No lower construction
is imported or assumed. -/
theorem five_mul_extremalNumber_five_le_two_choose (n : ℕ) :
    5 * extremalNumber 5 n ≤ 2 * n.choose 2 := by
  classical
  have hbound : extremalNumber 5 n ≤ (2 * n.choose 2) / 5 := by
    unfold extremalNumber
    apply Finset.sup_le
    intro G _hG
    split_ifs with hfree
    · apply (Nat.le_div_iff_mul_le (by decide : 0 < 5)).mpr
      simpa [Nat.mul_comm] using five_mul_card_le_two_choose G hfree
    · exact Nat.zero_le _
  calc
    5 * extremalNumber 5 n ≤ 5 * ((2 * n.choose 2) / 5) :=
      Nat.mul_le_mul_left 5 hbound
    _ ≤ 2 * n.choose 2 := Nat.mul_div_le _ _

#print axioms five_mul_card_le_two_choose
#print axioms five_mul_extremalNumber_five_le_two_choose

end
end Erdos1076Upper
