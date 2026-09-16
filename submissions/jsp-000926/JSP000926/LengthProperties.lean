/-
Copyright (c) 2026. Released under the Apache 2.0 license.

Basic length properties supporting the geometric extension of JSP-000926.
Prepared with OpenAI Codex assistance. The length and geometric counterexample
are defined in GeometricLength; this file proves that finite disjoint subarc
lengths do not overcount the length of a containing compact parameter interval.
-/
import JSP000926.GeometricLength

open Filter Set Topology
open scoped ENNReal Topology

namespace Erdos1115

lemma geometricLengthInDisc_mono (gamma : ℝ → ℂ) :
    Monotone (geometricLengthInDisc gamma) := by
  intro r s hrs
  unfold geometricLengthInDisc
  refine iSup_le fun n ↦ iSup_le fun a ↦ iSup_le fun b ↦ iSup_le fun h ↦ ?_
  have hs : DiscSubarcs gamma s a b := by
    refine ⟨?_, h.2⟩
    intro i
    exact ⟨(h.1 i).1, (h.1 i).2.1,
      fun t ht ↦ lt_of_lt_of_le ((h.1 i).2.2 t ht) hrs⟩
  exact le_iSup_of_le n (le_iSup_of_le a (le_iSup_of_le b
    (le_iSup_of_le hs le_rfl)))

/-- Ordered subintervals, possibly sharing endpoints, cannot overcount the
total variation on their containing interval. No continuity is needed. -/
lemma sum_ordered_subarc_variation_le (gamma : ℝ → ℂ) :
    ∀ (n : ℕ) (a b : Fin n → ℝ) (B : ℝ), 0 ≤ B →
      (∀ i, 0 ≤ a i) → (∀ i, a i ≤ b i) →
      (∀ i j, i < j → b i ≤ a j) → (∀ i, b i ≤ B) →
      (∑ i : Fin n, eVariationOn gamma (Set.Icc (a i) (b i))) ≤
        eVariationOn gamma (Set.Icc 0 B) := by
  intro n
  induction n with
  | zero =>
      intro a b B hB ha hab horder hb
      simp
  | succ n ih =>
      intro a b B hB ha hab horder hb
      have hhead := ih (fun i ↦ a i.castSucc) (fun i ↦ b i.castSucc)
        (a (Fin.last n)) (ha (Fin.last n))
        (fun i ↦ ha i.castSucc) (fun i ↦ hab i.castSucc)
        (fun i j hij ↦ horder i.castSucc j.castSucc hij)
        (fun i ↦ horder i.castSucc (Fin.last n) (Fin.castSucc_lt_last i))
      have htail : eVariationOn gamma (Set.Icc (a (Fin.last n)) (b (Fin.last n))) ≤
          eVariationOn gamma (Set.Icc (a (Fin.last n)) B) :=
        eVariationOn.mono gamma (Set.Icc_subset_Icc le_rfl (hb (Fin.last n)))
      have hsplit : eVariationOn gamma (Set.Icc 0 (a (Fin.last n))) +
          eVariationOn gamma (Set.Icc (a (Fin.last n)) B) =
          eVariationOn gamma (Set.Icc 0 B) := by
        simpa only [Set.univ_inter] using
          (eVariationOn.Icc_add_Icc gamma (s := Set.univ) (ha (Fin.last n))
            ((hab (Fin.last n)).trans (hb (Fin.last n))) (Set.mem_univ _))
      rw [Fin.sum_univ_castSucc]
      exact (add_le_add hhead htail).trans_eq hsplit

/-- If all nonnegative times in the disk lie before `B`, localized length is
bounded by ordinary total variation on `[0,B]`. This is a uniform bound over
all finite subarc families, rather than mere finiteness of individual terms. -/
lemma geometricLengthInDisc_le_variation_of_time_bound {gamma : ℝ → ℂ}
    {r B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖gamma t‖ < r → t ≤ B) :
    geometricLengthInDisc gamma r ≤ eVariationOn gamma (Set.Icc 0 B) := by
  unfold geometricLengthInDisc
  refine iSup_le fun n ↦ iSup_le fun a ↦ iSup_le fun b ↦ iSup_le fun h ↦ ?_
  apply sum_ordered_subarc_variation_le gamma n a b B hB
    (fun i ↦ (h.1 i).1) (fun i ↦ (h.1 i).2.1) h.2
  intro i
  exact hbound (b i) ((h.1 i).1.trans (h.1 i).2.1)
    ((h.1 i).2.2 (b i) ⟨(h.1 i).2.1, le_rfl⟩)

/-- Every disk has finite length for a locally rectifiable escaping curve.
Local rectifiability is expressed by Mathlib's locally bounded variation on
the nonnegative parameter half-line. Continuity is not needed for this bound. -/
theorem geometricLengthInDisc_ne_top_of_locallyBoundedVariationOn
    {gamma : ℝ → ℂ} (hlocal : LocallyBoundedVariationOn gamma (Set.Ici 0))
    (hescape : Tendsto (fun t ↦ ‖gamma t‖) atTop atTop) (r : ℝ) :
    geometricLengthInDisc gamma r ≠ ⊤ := by
  obtain ⟨A, hA⟩ := eventually_atTop.1
    (hescape.eventually (eventually_ge_atTop r))
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ t : ℝ, 0 ≤ t → ‖gamma t‖ < r → t ≤ B := by
    intro t ht hinside
    by_contra hnot
    have hBt : B < t := lt_of_not_ge hnot
    exact (not_lt_of_ge (hA t ((le_max_left A 0).trans hBt.le))) hinside
  have hvariation : eVariationOn gamma (Set.Icc 0 B) ≠ ⊤ := by
    have h := hlocal 0 B (by simp) hB
    have hinter : Set.Ici (0 : ℝ) ∩ Set.Icc 0 B = Set.Icc 0 B := by
      exact Set.inter_eq_right.mpr (fun t ht ↦ ht.1)
    simpa only [BoundedVariationOn, hinter] using h
  exact ne_top_of_le_ne_top hvariation
    (geometricLengthInDisc_le_variation_of_time_bound hB hbound)

#print axioms geometricLengthInDisc_mono
#print axioms geometricLengthInDisc_ne_top_of_locallyBoundedVariationOn

end Erdos1115
