import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum

/-!
# The composite-successor obstruction for Erdős problem 835

Mathematical result: Jie Ma and Quanyu Tang, *On Problem 835*.
This file formalizes a necessary condition, not a solution of the open problem.
-/

open Finset
open scoped BigOperators

namespace Prize835

variable {α : Type*} [DecidableEq α]

/-- Count the fixed-size subsets of `U` containing a prescribed subset `L`. -/
theorem card_containing (U L : Finset α) (r : ℕ)
    (hLU : L ⊆ U) (hLr : L.card ≤ r) :
    ((U.powersetCard r).filter (L ⊆ ·)).card =
      (U.card - L.card).choose (r - L.card) := by
  rw [← card_sdiff_of_subset hLU, ← card_powersetCard]
  apply card_bij (fun S _ => S \ L)
  · intro S hS
    rcases mem_filter.mp hS with ⟨hS, hLS⟩
    rcases mem_powersetCard.mp hS with ⟨hSU, hSr⟩
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff hSU (Subset.refl _),
      by rw [card_sdiff_of_subset hLS, hSr]⟩
  · intro S hS T hT hST
    have hLS := (mem_filter.mp hS).2
    have hLT := (mem_filter.mp hT).2
    have hs : L ∪ (S \ L) = S := union_sdiff_of_subset hLS
    have ht : L ∪ (T \ L) = T := union_sdiff_of_subset hLT
    rw [← hs, ← ht, hST]
  · intro D hD
    rcases mem_powersetCard.mp hD with ⟨hDU, hDr⟩
    have hdis : Disjoint L D := by
      apply disjoint_left.mpr
      intro x hxL hxD
      exact (mem_sdiff.mp (hDU hxD)).2 hxL
    refine ⟨L ∪ D, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩,
      subset_union_left⟩, ?_⟩
    · exact union_subset hLU (hDU.trans sdiff_subset)
    · rw [card_union_of_disjoint hdis, hDr]
      omega
    · ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · tauto
      · intro hx
        exact ⟨Or.inr hx, (mem_sdiff.mp (hDU hx)).2⟩

/-- The original finite-set colouring property, with a total colour function.
Only its values on sets of cardinality `k` are used. -/
def Rainbow (k : ℕ) (c : Finset (Fin (2 * k)) → Fin (k + 1)) : Prop :=
  ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
    ∀ j, ∃ S ∈ A.powersetCard k, c S = j

theorem window_injective {k : ℕ} {c : Finset (Fin (2 * k)) → Fin (k + 1)}
    (hc : Rainbow k c) (A : Finset (Fin (2 * k))) (hA : A.card = k + 1) :
    Set.InjOn c (A.powersetCard k) := by
  apply Finset.injOn_of_surjOn_of_card_le c
    (t := (univ : Finset (Fin (k + 1))))
  · intro S _; simp
  · intro j _
    obtain ⟨S, hS, hSj⟩ := hc A hA j
    exact ⟨S, hS, hSj⟩
  · simp [card_powersetCard, hA, Nat.choose_succ_self_right]

/-- Each bottom clique has exactly one extension of each colour. -/
theorem unique_extension {k : ℕ} (hk : 1 ≤ k)
    {c : Finset (Fin (2 * k)) → Fin (k + 1)} (hc : Rainbow k c)
    (R : Finset (Fin (2 * k))) (hR : R.card = k - 1) (j : Fin (k + 1)) :
    ∃! S : Finset (Fin (2 * k)), S.card = k ∧ R ⊆ S ∧ c S = j := by
  classical
  let E := ((univ : Finset (Fin (2 * k))).powersetCard k).filter (R ⊆ ·)
  have hmem : ∀ S, S ∈ E ↔ S.card = k ∧ R ⊆ S := by
    intro S; simp [E]
  have hcard : E.card = k + 1 := by
    dsimp [E]
    rw [card_containing _ _ _ (subset_univ _) (by omega), card_univ,
      Fintype.card_fin, hR]
    have h1 : 2 * k - (k - 1) = k + 1 := by omega
    have h2 : k - (k - 1) = 1 := by omega
    rw [h1, h2, Nat.choose_one_right]
  have hinj : Set.InjOn c E := by
    intro S hS T hT hcol
    rcases (hmem S).mp hS with ⟨hSk, hRS⟩
    rcases (hmem T).mp hT with ⟨hTk, hRT⟩
    have hRi : R ⊆ S ∩ T := subset_inter hRS hRT
    have hi := card_le_card hRi
    have hu := card_union_add_card_inter S T
    have hbound : (S ∪ T).card ≤ k + 1 := by omega
    obtain ⟨A, huA, _, hA⟩ := exists_subsuperset_card_eq
      (subset_univ (S ∪ T)) hbound (show k + 1 ≤ (univ : Finset (Fin (2 * k))).card by simp; omega)
    apply window_injective hc A hA
      (mem_powersetCard.mpr ⟨subset_union_left.trans huA, hSk⟩)
      (mem_powersetCard.mpr ⟨subset_union_right.trans huA, hTk⟩) hcol
  have hsurj : Set.SurjOn c E (univ : Finset (Fin (k + 1))) := by
    apply Finset.surjOn_of_injOn_of_card_le c (fun _ _ => by simp) hinj
    simp [hcard]
  obtain ⟨S, hS, hSj⟩ := hsurj (mem_univ j)
  refine ⟨S, ⟨((hmem S).mp hS).1, ((hmem S).mp hS).2, hSj⟩, ?_⟩
  intro T hT
  exact hinj ((hmem T).mpr ⟨hT.1, hT.2.1⟩) hS (hT.2.2.trans hSj.symm)

/-- The exact-design divisibility obstruction for every `1 ≤ t ≤ k`. -/
theorem rainbow_divisibility {k : ℕ} (hk : 1 ≤ k)
    {c : Finset (Fin (2 * k)) → Fin (k + 1)} (hc : Rainbow k c)
    {t : ℕ} (ht : 1 ≤ t) (htk : t ≤ k) : t ∣ (k + t).choose (t - 1) := by
  classical
  obtain ⟨L, _, hL⟩ := exists_subset_card_eq
    (show k - t ≤ (univ : Finset (Fin (2 * k))).card by simp; omega)
  let Rs := ((univ : Finset (Fin (2 * k))).powersetCard (k - 1)).filter (L ⊆ ·)
  let Bs := (((univ : Finset (Fin (2 * k))).powersetCard k).filter
    (fun S => L ⊆ S ∧ c S = 0))
  have hRm : ∀ R, R ∈ Rs ↔ R.card = k - 1 ∧ L ⊆ R := by
    intro R; simp [Rs]
  have hBm : ∀ S, S ∈ Bs ↔ S.card = k ∧ L ⊆ S ∧ c S = 0 := by
    intro S; simp [Bs]
  have hrow : ∀ R ∈ Rs, (Bs.bipartiteAbove (· ⊆ ·) R).card = 1 := by
    intro R hR
    rcases (hRm R).mp hR with ⟨hRk, hLR⟩
    obtain ⟨S, hS, huniq⟩ := unique_extension hk hc R hRk 0
    have heq : Bs.bipartiteAbove (· ⊆ ·) R = {S} := by
      ext T
      simp only [mem_bipartiteAbove, mem_singleton]
      constructor
      · rintro ⟨hT, hRT⟩
        exact huniq T ⟨((hBm T).mp hT).1, hRT, ((hBm T).mp hT).2.2⟩
      · intro hTS
        subst T
        exact ⟨(hBm S).mpr ⟨hS.1, hLR.trans hS.2.1, hS.2.2⟩, hS.2.1⟩
    rw [heq, card_singleton]
  have hcol : ∀ S ∈ Bs, (Rs.bipartiteBelow (· ⊆ ·) S).card = t := by
    intro S hS
    rcases (hBm S).mp hS with ⟨hSk, hLS, _⟩
    have heq : Rs.bipartiteBelow (· ⊆ ·) S =
        (S.powersetCard (k - 1)).filter (L ⊆ ·) := by
      ext R
      simp only [mem_bipartiteBelow, hRm, mem_filter, mem_powersetCard]
      tauto
    rw [heq, card_containing _ _ _ hLS (by omega), hSk, hL]
    have h1 : k - (k - t) = t := by omega
    have h2 : k - 1 - (k - t) = t - 1 := by omega
    rw [h1, h2, Nat.choose_symm (by omega)]
    exact Nat.choose_one_right t
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun R S : Finset (Fin (2 * k)) => R ⊆ S) (s := Rs) (t := Bs)
  have hc1 : (∑ R ∈ Rs, (Bs.bipartiteAbove (· ⊆ ·) R).card) = Rs.card := by
    rw [sum_congr rfl hrow]
    simp
  have hc2 : (∑ S ∈ Bs, (Rs.bipartiteBelow (· ⊆ ·) S).card) = Bs.card * t := by
    rw [sum_congr rfl hcol]
    simp
  rw [hc1, hc2] at hcount
  have hRcard : Rs.card = (k + t).choose (t - 1) := by
    dsimp [Rs]
    rw [card_containing _ _ _ (subset_univ _) (by omega), card_univ,
      Fintype.card_fin, hL]
    congr 1 <;> omega
  rw [hRcard] at hcount
  exact ⟨Bs.card, by rw [hcount, Nat.mul_comm]⟩

/-- The binomial obstruction detects every composite successor. -/
theorem prime_of_divisibility {k : ℕ} (hk : 1 ≤ k)
    (hd : ∀ t, 1 ≤ t → t ≤ k → t ∣ (k + t).choose (t - 1)) :
    (k + 1).Prime := by
  by_contra hn
  let p := (k + 1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ k + 1 := Nat.minFac_dvd _
  have hpk : p ≤ k := by
    have hle := Nat.minFac_le (show 0 < k + 1 by omega)
    have hne : p ≠ k + 1 := by
      intro heq
      exact hn (heq ▸ hp)
    omega
  have hp1 := hp.one_lt
  have hm : (k + p) % p = p - 1 := by
    have hz := Nat.mod_eq_zero_of_dvd hpd
    have hb := Nat.mod_lt k hp.pos
    have hadd := Nat.add_mod k 1 p
    rw [Nat.mod_eq_of_lt hp1] at hadd
    have : k % p + 1 ≤ p := by omega
    have : k % p + 1 = p := by
      by_contra hne
      have hlt : k % p + 1 < p := by omega
      rw [Nat.mod_eq_of_lt hlt] at hadd
      omega
    simpa [Nat.add_mod] using (show k % p = p - 1 by omega)
  letI : Fact p.Prime := ⟨hp⟩
  have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := k + p) (k := p - 1) (p := p)
  have hlt : p - 1 < p := by omega
  simp only [hm, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt,
    Nat.choose_self, Nat.choose_zero_right, mul_one] at hLucas
  have hzero := Nat.mod_eq_zero_of_dvd (hd p (by omega) hpk)
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  change (k + p).choose (p - 1) % p = 1 % p at hLucas
  omega

/-- Ma–Tang's general composite-successor exclusion, in colouring form. -/
theorem rainbow_successor_prime {k : ℕ} (hk : 1 ≤ k)
    {c : Finset (Fin (2 * k)) → Fin (k + 1)} (hc : Rainbow k c) :
    (k + 1).Prime :=
  prime_of_divisibility hk (fun _ ht htk => rainbow_divisibility hk hc ht htk)

end Prize835

/- The following definition is reproduced from Formal Conjectures, Erdős 835,
commit 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
Copyright 2025 The Formal Conjectures Authors. Apache-2.0.
Only the definition is reproduced; none of that file's unproved theorems is imported.
-/
namespace Erdos835

def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))

/-- Exact-source statement: the colouring property forces a prime successor. -/
theorem property_successor_prime {k : ℕ} (hk : 1 ≤ k) (h : Property k) :
    (k + 1).Prime := by
  classical
  obtain ⟨c, hc⟩ := h
  let C : Finset (Fin (2 * k)) → Fin (k + 1) :=
    fun S => if hS : S.card = k then c ⟨S, hS⟩ else 0
  apply Prize835.rainbow_successor_prime hk (c := C)
  intro A hA j
  have hj : j ∈ image c {s : {s : Finset (Fin (2 * k)) // s.card = k} | s.val ⊂ A} := by
    rw [hc A hA]; exact mem_univ _
  obtain ⟨S, hS, hSj⟩ := mem_image.mp hj
  have hSA : S.val ⊂ A := (mem_filter.mp hS).2
  refine ⟨S.val, mem_powersetCard.mpr ⟨hSA.subset, S.property⟩, ?_⟩
  simpa [C, S.property] using hSj

/-- All composite successors are excluded; prime successors remain open here. -/
theorem not_property_of_composite {k : ℕ} (hk : 1 ≤ k)
    (hc : ¬ (k + 1).Prime) : ¬ Property k :=
  fun h => hc (property_successor_prime hk h)

/-- An even parameter outside the small range `3 ≤ k ≤ 8`. -/
theorem not_property_fourteen : ¬ Property 14 :=
  not_property_of_composite (by decide) (by decide)

#print axioms property_successor_prime
#print axioms not_property_of_composite
#print axioms not_property_fourteen

end Erdos835
