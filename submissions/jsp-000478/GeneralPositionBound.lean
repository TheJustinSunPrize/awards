import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
The classical greedy bound for Erdős 589 / JSP-000478.
The stronger asymptotic bounds and the optimal growth question are not claimed.
All collinearity statements use Mathlib's standard affine-space definition.
-/

open Finset
open scoped BigOperators

namespace GeneralPositionBound

abbrev Point := ℝ × ℝ

def BoundedLines (a : Finset Point) (m : ℕ) : Prop :=
  ∀ s : Finset Point, s ⊆ a → Collinear ℝ (s : Set Point) → s.card ≤ m

abbrev NoFour (a : Finset Point) := BoundedLines a 3
abbrev NoThree (a : Finset Point) := BoundedLines a 2

theorem boundedLines_iff (a : Finset Point) (m : ℕ) :
    BoundedLines a m ↔
      ∀ s : Finset Point, s ⊆ a → s.card = m + 1 → ¬ Collinear ℝ (s : Set Point) := by
  constructor
  · intro h s hs hc hcol
    have := h s hs hcol
    omega
  · intro h s hs hcol
    by_contra hn
    obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (by omega : m + 1 ≤ s.card)
    exact h t (hts.trans hs) ht (hcol.subset (by exact_mod_cast hts))

theorem noThree_empty : NoThree (∅ : Finset Point) := by
  intro s hs _
  have he : s = ∅ := Finset.subset_empty.mp hs
  simp [he]

theorem collinear_span {s : Set Point} (hs : Collinear ℝ s) :
    Collinear ℝ (affineSpan ℝ s : Set Point) := by
  unfold Collinear
  rw [← AffineSubspace.direction_eq_vectorSpan, direction_affineSpan]
  exact hs

theorem pair_span_collinear (p : Finset Point) (hp : p.card = 2) :
    Collinear ℝ (affineSpan ℝ (p : Set Point) : Set Point) := by
  obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp hp
  exact collinear_span (by simpa using collinear_pair ℝ x y)

theorem maximal_general_position (a : Finset Point) :
    ∃ b ⊆ a, NoThree b ∧
      ∀ s : Finset Point, s ⊆ a → NoThree s → s.card ≤ b.card := by
  classical
  let good := a.powerset.filter NoThree
  have hne : good.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [good, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset a, noThree_empty⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image good Finset.card hne
  have hb' := Finset.mem_filter.mp hb
  refine ⟨b, Finset.mem_powerset.mp hb'.1, hb'.2, ?_⟩
  intro s hs hsf
  exact hmax s (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hsf⟩)

theorem outside_on_pair (a b : Finset Point) (hb : b ⊆ a) (hgp : NoThree b)
    (hmax : ∀ s : Finset Point, s ⊆ a → NoThree s → s.card ≤ b.card)
    {x : Point} (hx : x ∈ a \ b) :
    ∃ p ∈ b.powersetCard 2, x ∈ affineSpan ℝ (p : Set Point) := by
  classical
  have hxa := (Finset.mem_sdiff.mp hx).1
  have hxb := (Finset.mem_sdiff.mp hx).2
  have hbad : ¬ NoThree (insert x b) := by
    intro h
    have hm := hmax (insert x b) (Finset.insert_subset hxa hb) h
    rw [Finset.card_insert_of_notMem hxb] at hm
    omega
  unfold NoThree BoundedLines at hbad
  push Not at hbad
  obtain ⟨s, hs, hcol, hcard⟩ := hbad
  have hxs : x ∈ s := by
    by_contra hn
    have hsb : s ⊆ b := by
      intro y hy
      rcases Finset.mem_insert.mp (hs hy) with he | he
      · subst y
        exact False.elim (hn hy)
      · exact he
    have := hgp s hsb hcol
    omega
  have herase : s.erase x ⊆ b := by
    intro y hy
    have hy' := Finset.mem_erase.mp hy
    rcases Finset.mem_insert.mp (hs hy'.2) with he | he
    · exact False.elim (hy'.1 he)
    · exact he
  have he := Finset.card_erase_add_one hxs
  obtain ⟨p, hps, hp2⟩ := Finset.exists_subset_card_eq
    (by omega : 2 ≤ (s.erase x).card)
  have hpb : p ⊆ b := hps.trans herase
  have hpt : p ⊆ s := hps.trans (Finset.erase_subset _ _)
  refine ⟨p, Finset.mem_powersetCard.mpr ⟨hpb, hp2⟩, ?_⟩
  obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp hp2
  have hu : u ∈ s := hpt (by simp [hp])
  have hv : v ∈ s := hpt (by simp [hp])
  have hxline := hcol.mem_affineSpan_of_mem_of_ne hu hv hxs huv
  simpa only [hp, Finset.coe_pair] using hxline

noncomputable section
open scoped Classical

def blocked (a b p : Finset Point) : Finset Point :=
  (a \ b).filter (fun x => x ∈ affineSpan ℝ (p : Set Point))

theorem blocked_card_le_one (a b : Finset Point) (ha : NoFour a)
    (hb : b ⊆ a) {p : Finset Point} (hp : p ∈ b.powersetCard 2) :
    (blocked a b p).card ≤ 1 := by
  obtain ⟨hpb, hp2⟩ := Finset.mem_powersetCard.mp hp
  have hsub : p ∪ blocked a b p ⊆ a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hb (hpb hx)
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
  have hline : Collinear ℝ ((p ∪ blocked a b p : Finset Point) : Set Point) := by
    apply (pair_span_collinear p hp2).subset
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact subset_affineSpan ℝ (p : Set Point) hx
    · exact (Finset.mem_filter.mp hx).2
  have hdis : Disjoint p (blocked a b p) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx').1).2 (hpb hx)
  have hc := ha (p ∪ blocked a b p) hsub hline
  rw [Finset.card_union_of_disjoint hdis, hp2] at hc
  omega

/-- Exact finite counting form of the classical greedy argument. -/
theorem greedy_bound (a : Finset Point) (ha : NoFour a) :
    ∃ b ⊆ a, NoThree b ∧ a.card ≤ b.card + Nat.choose b.card 2 := by
  obtain ⟨b, hb, hgp, hmax⟩ := maximal_general_position a
  refine ⟨b, hb, hgp, ?_⟩
  have hcover : a \ b ⊆ (b.powersetCard 2).biUnion (blocked a b) := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := outside_on_pair a b hb hgp hmax hx
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hx, hxp⟩⟩
  have hc : (a \ b).card ≤ (b.powersetCard 2).card := by
    calc
      _ ≤ ((b.powersetCard 2).biUnion (blocked a b)).card := Finset.card_le_card hcover
      _ ≤ ∑ p ∈ b.powersetCard 2, (blocked a b p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ b.powersetCard 2, 1 :=
        Finset.sum_le_sum (fun p hp => blocked_card_le_one a b ha hb hp)
      _ = _ := by simp
  rw [Finset.card_powersetCard] at hc
  have he := Finset.card_sdiff_add_card_eq_card hb
  omega

theorem greedy_quadratic_bound (a : Finset Point) (ha : NoFour a) :
    ∃ b ⊆ a, NoThree b ∧ 2 * a.card ≤ b.card * (b.card + 1) := by
  obtain ⟨b, hb, hgp, hcard⟩ := greedy_bound a ha
  refine ⟨b, hb, hgp, ?_⟩
  have hreal : (a.card : ℝ) ≤ (b.card : ℝ) + (Nat.choose b.card 2 : ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_choose_two] at hreal
  have hreal' : (2 : ℝ) * (a.card : ℝ) ≤ (b.card : ℝ) * ((b.card : ℝ) + 1) := by
    nlinarith
  exact_mod_cast hreal'

theorem greedy_square_bound (a : Finset Point) (ha : NoFour a) :
    ∃ b ⊆ a, NoThree b ∧ a.card ≤ b.card ^ 2 := by
  obtain ⟨b, hb, hgp, hc⟩ := greedy_quadratic_bound a ha
  refine ⟨b, hb, hgp, ?_⟩
  by_cases hz : b.card = 0
  · simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0)] at *
    omega
  · have hpos : 1 ≤ b.card := by omega
    nlinarith

end
end GeneralPositionBound
