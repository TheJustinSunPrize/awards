/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Prepared with OpenAI Codex assistance.

The half-line curve interface to the attributed geometric extension.
-/
import JSP000926.GeometricLength

open Filter Set Topology
open scoped ENNReal Topology

namespace Erdos1115

lemma geometricLengthInDisc_le_of_eqOn_nonneg {gamma delta : ℝ → ℂ}
    (h : EqOn gamma delta (Ici 0)) (r : ℝ) :
    geometricLengthInDisc gamma r ≤ geometricLengthInDisc delta r := by
  unfold geometricLengthInDisc
  refine iSup_le fun n ↦ iSup_le fun a ↦ iSup_le fun b ↦ iSup_le fun hf ↦ ?_
  have hfd : DiscSubarcs delta r a b := by
    refine ⟨?_, hf.2⟩
    intro i
    refine ⟨(hf.1 i).1, (hf.1 i).2.1, ?_⟩
    intro t ht
    rw [← h (le_trans (hf.1 i).1 ht.1)]
    exact (hf.1 i).2.2 t ht
  refine le_iSup_of_le n (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hfd ?_)))
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact eVariationOn.eq_of_eqOn fun t ht ↦ h (le_trans (hf.1 i).1 ht.1)

lemma geometricLengthInDisc_eq_of_eqOn_nonneg {gamma delta : ℝ → ℂ}
    (h : EqOn gamma delta (Ici 0)) (r : ℝ) :
    geometricLengthInDisc gamma r = geometricLengthInDisc delta r :=
  le_antisymm (geometricLengthInDisc_le_of_eqOn_nonneg h r)
    (geometricLengthInDisc_le_of_eqOn_nonneg h.symm r)

/-- Escape of the entire function along a curve forces the curve itself to
leave every bounded disk. This removes an apparent extra assumption. -/
lemma curve_escapes_of_composition_escapes {f : ℂ → ℂ} (hf : Continuous f)
    {gamma : ℝ → ℂ} (hfg : Tendsto (fun t ↦ ‖f (gamma t)‖) atTop atTop) :
    Tendsto (fun t ↦ ‖gamma t‖) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuousOn
  filter_upwards [hfg.eventually (eventually_gt_atTop M)] with t ht
  by_contra hnot
  have hnorm : ‖gamma t‖ ≤ R := (lt_of_not_ge hnot).le
  have hmem : gamma t ∈ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact (not_lt_of_ge (hM _ hmem)) ht

/-- Main negative resolution for continuous half-line curves. Only the
divergence of f along the curve is assumed. No condition is put on negative
parameters, and no speed bound or arclength reparametrization is required. -/
theorem not_erdos_1115_continuousOn :
    ∀ phi : ℝ → ℝ, Tendsto phi atTop atTop →
      ∃ f : ℂ → ℂ,
        (∃ z w : ℂ, f z ≠ f w) ∧
        ¬Bornology.IsBounded (Set.range f) ∧
        EntireOfFiniteOrder f ∧
        HasGolbergEremenkoGrowth phi f ∧
        HasGeometricEscapingBarriers f ∧
        ∀ gamma : ℝ → ℂ, ContinuousOn gamma (Ici 0) →
          Tendsto (fun t ↦ ‖f (gamma t)‖) atTop atTop →
          ¬HasLinearGeometricLength gamma := by
  intro phi hphi
  obtain ⟨f, hnonconstant, hunbounded, hfinite, hgrowth, hbarriers, hcurves⟩ :=
    not_erdos_1115_geometric phi hphi
  refine ⟨f, hnonconstant, hunbounded, hfinite, hgrowth, hbarriers, ?_⟩
  intro gamma hgamma hfg hlinear
  let delta : ℝ → ℂ := fun t ↦ gamma (max 0 t)
  have hdelta : Continuous delta :=
    hgamma.comp_continuous (continuous_const.max continuous_id)
      (fun t ↦ (show (0 : ℝ) ≤ max 0 t from le_max_left _ _))
  have heq : EqOn delta gamma (Ici 0) := by
    intro t ht
    exact congrArg gamma (max_eq_right ht)
  have hfgdelta : Tendsto (fun t ↦ ‖f (delta t)‖) atTop atTop := by
    apply hfg.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [heq ht]
  have hescape : EscapesAlong f delta :=
    ⟨curve_escapes_of_composition_escapes hfinite.1.continuous hfgdelta, hfgdelta⟩
  apply hcurves delta hdelta hescape
  obtain ⟨C, hC, hbound⟩ := hlinear
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with r hr
  rw [geometricLengthInDisc_eq_of_eqOn_nonneg heq]
  exact hr

#print axioms curve_escapes_of_composition_escapes
#print axioms not_erdos_1115_continuousOn

end Erdos1115
