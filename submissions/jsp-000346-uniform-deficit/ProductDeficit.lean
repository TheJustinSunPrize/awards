/-
Copyright (c) 2026 green3sf. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: green3sf (AI-assisted development)
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform omission bounds for distinct consecutive products

Scoped supplement for JSP-000346 / Erdős 421. This file proves a necessary
condition; it does not construct a density-one sequence or solve the full
existence problem.

The proof counts adjacent products of the elements in B ∩ (sqrt(m), m].
They are distinct missing values above m. Counting them together with the
omissions up to m avoids any assumption on the density of B.

Comparison source: Kyle Pratt, A “Digested” Proof of Erdős Problem #421,
Proposition 7.1, https://www.erdosproblems.com/static/421-Pratt.pdf.
The stronger finite estimate here and the Lean code were developed for this
submission. No global priority claim is made.
-/

open Finset
namespace ProductDeficit

/-- Adjacent members of B never have their product in B. -/
def AvoidsAdjacentProducts (B : Set ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x < y →
    (∀ z ∈ B, x < z → z < y → False) → x * y ∉ B

/-- Number of positive integers at most N omitted by B. -/
noncomputable def deficit (B : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Icc 1 N).filter (fun x => x ∉ B)).card

/-- A uniform finite deficit bound, with no density assumption. -/
theorem finite_bound (B : Set ℕ) (hB : AvoidsAdjacentProducts B)
    (N m t : ℕ) (hmN : m * m ≤ N) (hmt : m < (t + 1) * (t + 1)) :
    m ≤ deficit B N + t + 1 := by
  classical
  let S := (Ioc t m).filter (fun x => x ∈ B)
  let L := (Icc 1 m).filter (fun x => x ∉ B)
  let e := S.orderEmbOfFin rfl
  have he_mem (i : Fin S.card) : t < e i ∧ e i ≤ m ∧ e i ∈ B := by
    have h := S.orderEmbOfFin_mem rfl i
    simpa only [S, mem_filter, mem_Ioc, and_assoc] using h
  have hcover : Icc 1 m ⊆ Icc 1 t ∪ S ∪ L := by
    intro x hx
    simp only [mem_Icc] at hx
    by_cases hxt : x ≤ t
    · exact mem_union_left _ (mem_union_left _ (mem_Icc.mpr ⟨hx.1, hxt⟩))
    · by_cases hxB : x ∈ B
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨by omega, hx.2⟩, hxB⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr hx, hxB⟩)
  have hcount : m ≤ t + S.card + L.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (Icc 1 t ∪ S) L
    have h3 := card_union_le (Icc 1 t) S
    simp only [Nat.card_Icc] at h1 h2 h3
    omega
  let left (i : Fin (S.card - 1)) : Fin S.card := ⟨i, by omega⟩
  let right (i : Fin (S.card - 1)) : Fin S.card := ⟨i + 1, by omega⟩
  let f (i : Fin (S.card - 1)) := e (left i) * e (right i)
  have hlt (i : Fin (S.card - 1)) : e (left i) < e (right i) :=
    e.strictMono (by simp [left, right])
  have hf_missing (i : Fin (S.card - 1)) : f i ∉ B := by
    apply hB _ (he_mem (left i)).2.2 _ (he_mem (right i)).2.2 (hlt i)
    intro z hz hxz hzy
    have hzS : z ∈ S := mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨lt_trans (he_mem (left i)).1 hxz,
       le_trans hzy.le (he_mem (right i)).2.1⟩, hz⟩
    let j := (S.orderIsoOfFin rfl).symm ⟨z, hzS⟩
    have hej : e j = z := by
      change ((S.orderIsoOfFin rfl) j : ℕ) = z
      exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨z, hzS⟩)
    have h1 : left i < j := e.lt_iff_lt.mp (by simpa [hej] using hxz)
    have h2 : j < right i := e.lt_iff_lt.mp (by simpa [hej] using hzy)
    change i.val < j.val at h1
    change j.val < i.val + 1 at h2
    omega
  have hf_large (i : Fin (S.card - 1)) : m < f i := by
    have hl := (he_mem (left i)).1
    have hr := (he_mem (right i)).1
    have hp := Nat.mul_le_mul (show t + 1 ≤ e (left i) by omega)
      (show t + 1 ≤ e (right i) by omega)
    exact lt_of_lt_of_le hmt hp
  have hf_small (i : Fin (S.card - 1)) : f i ≤ N :=
    le_trans (Nat.mul_le_mul (he_mem (left i)).2.1 (he_mem (right i)).2.1) hmN
  have hf_mono : StrictMono f := by
    intro i j hij
    have hl : e (left i) < e (left j) := e.strictMono (by simpa [left] using hij)
    have hr : e (right i) < e (right j) := e.strictMono (by simpa [right] using hij)
    have hp : 0 < e (right i) := lt_of_le_of_lt (Nat.zero_le t) (he_mem (right i)).1
    exact Nat.mul_lt_mul_of_lt_of_le hl hr.le (lt_trans hp hr)
  let T := univ.image f
  have hTcard : T.card = S.card - 1 := by
    rw [card_image_of_injective _ hf_mono.injective]
    simp
  have hLT : Disjoint L T := by
    apply disjoint_left.mpr
    intro x hxL hxT
    obtain ⟨i, _, rfl⟩ := mem_image.mp hxT
    have h1 := (mem_Icc.mp (mem_filter.mp hxL).1).2
    have h2 := hf_large i
    omega
  have hmle : m ≤ N := le_trans (Nat.le_mul_self m) hmN
  have hsub : L ∪ T ⊆ (Icc 1 N).filter (fun x => x ∉ B) := by
    intro x hx
    rcases mem_union.mp hx with hxL | hxT
    · obtain ⟨hxm, hxB⟩ := mem_filter.mp hxL
      obtain ⟨hx1, hxm⟩ := mem_Icc.mp hxm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hx1, le_trans hxm hmle⟩, hxB⟩
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxT
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := hf_large i; omega, hf_small i⟩,
        hf_missing i⟩
  have hsum : L.card + T.card ≤ deficit B N := by
    simpa only [card_union_of_disjoint hLT, deficit] using card_le_card hsub
  omega

/-- Explicit square-root obstruction for every set satisfying the adjacency condition. -/
theorem sqrt_bound (B : Set ℕ) (hB : AvoidsAdjacentProducts B) (N : ℕ) :
    N.sqrt ≤ deficit B N + N.sqrt.sqrt + 1 :=
  finite_bound B hB N N.sqrt N.sqrt.sqrt (Nat.sqrt_le N) (Nat.lt_succ_sqrt _)

/-- The original distinct-products requirement for nonempty consecutive index intervals. -/
def DistinctBlockProducts (a : ℕ → ℕ) : Prop :=
  ∀ u v u' v' : ℕ, u ≤ v → u' ≤ v' →
    (∏ i ∈ Icc u v, a i) = (∏ i ∈ Icc u' v', a i) → u = u' ∧ v = v'

/-- Statement bridge: the original block condition implies the weaker adjacency condition. -/
theorem avoids_of_distinct_blocks (a : ℕ → ℕ) (ha : StrictMono a)
    (hd : DistinctBlockProducts a) : AvoidsAdjacentProducts (Set.range a) := by
  intro x hx y hy hxy hadj
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij : i < j := ha.lt_iff_lt.mp hxy
  have hji : j = i + 1 := by
    by_contra hne
    have hij' : i + 1 < j := by omega
    exact hadj (a (i + 1)) ⟨i + 1, rfl⟩ (ha (by omega)) (ha hij')
  subst j
  rintro ⟨k, hk⟩
  have hprod : (∏ n ∈ Icc i (i + 1), a n) = ∏ n ∈ Icc k k, a n := by
    rw [prod_Icc_succ_top (by omega : i ≤ i + 1)]
    simpa using hk.symm
  obtain ⟨h1, h2⟩ := hd i (i + 1) k k (by omega) (by omega) hprod
  omega

/-- Uniform obstruction for the actual sequence statement in Erdős 421 / JSP-000346. -/
theorem sequence_sqrt_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hd : DistinctBlockProducts a) (N : ℕ) :
    N.sqrt ≤ deficit (Set.range a) N + N.sqrt.sqrt + 1 :=
  sqrt_bound (Set.range a) (avoids_of_distinct_blocks a ha hd) N

/-- The block predicate agrees with the injectivity formulation used by formal-conjectures. -/
theorem distinct_blocks_iff_injOn (a : ℕ → ℕ) :
    DistinctBlockProducts a ↔
      {p : ℕ × ℕ | p.1 ≤ p.2}.InjOn (fun p => ∏ i ∈ Icc p.1 p.2, a i) := by
  constructor
  · intro h p hp q hq heq
    exact Prod.ext (h p.1 p.2 q.1 q.2 hp hq heq).1 (h p.1 p.2 q.1 q.2 hp hq heq).2
  · intro h u v u' v' huv hu'v' heq
    have he := h (x₁ := (u, v)) huv (x₂ := (u', v')) hu'v' heq
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- The finite deficit bound with the original nonempty-index-interval injectivity hypothesis. -/
theorem original_statement_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hd : {p : ℕ × ℕ | p.1 ≤ p.2}.InjOn
      (fun p => ∏ i ∈ Icc p.1 p.2, a i)) (N : ℕ) :
    N.sqrt ≤ deficit (Set.range a) N + N.sqrt.sqrt + 1 :=
  sequence_sqrt_bound a ha ((distinct_blocks_iff_injOn a).mpr hd) N

/-- An entirely natural-number formulation of the asymptotic coefficient one.
For each k >= 1, all N >= (2k)^4 have deficit at least (1-1/k) floor(sqrt N). -/
theorem coefficient_one_bound (B : Set ℕ) (hB : AvoidsAdjacentProducts B)
    (k N : ℕ) (hk : 1 ≤ k) (hN : (2 * k) ^ 4 ≤ N) :
    (k - 1) * N.sqrt ≤ k * deficit B N := by
  have hm : (2 * k) ^ 2 ≤ N.sqrt := Nat.le_sqrt'.mpr (by
    calc
      ((2 * k) ^ 2) ^ 2 = (2 * k) ^ 4 := by rw [← pow_mul]
      _ ≤ N := hN)
  have ht : 2 * k ≤ N.sqrt.sqrt := Nat.le_sqrt'.mpr hm
  have hs := Nat.sqrt_le N.sqrt
  have he : k * (N.sqrt.sqrt + 1) ≤ N.sqrt := by
    have h1 := Nat.mul_le_mul_left N.sqrt.sqrt ht
    have h2 := Nat.mul_le_mul_left k (show 1 ≤ N.sqrt.sqrt by omega)
    nlinarith
  have hb := sqrt_bound B hB N
  have hb' := Nat.mul_le_mul_left k hb
  have hk' : k - 1 + 1 = k := by omega
  nlinarith

/-- The all-parameter coefficient-one result for the original sequence property. -/
theorem sequence_coefficient_one_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hd : DistinctBlockProducts a) (k N : ℕ) (hk : 1 ≤ k)
    (hN : (2 * k) ^ 4 ≤ N) :
    (k - 1) * N.sqrt ≤ k * deficit (Set.range a) N :=
  coefficient_one_bound (Set.range a) (avoids_of_distinct_blocks a ha hd) k N hk hN

#print axioms finite_bound
#print axioms sqrt_bound
#print axioms avoids_of_distinct_blocks
#print axioms sequence_sqrt_bound
#print axioms distinct_blocks_iff_injOn
#print axioms original_statement_bound
#print axioms coefficient_one_bound
#print axioms sequence_coefficient_one_bound

end ProductDeficit
