/-
Closed-lemniscate extension for JSP-000410.

This module contains a new assembly of the closed-component statement. It imports,
rather than redistributes, the upstream open-component development:
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos511.lean

The construction and analytic estimates are due to that upstream formalization,
which credits Pommerenke and Huang for the mathematical result and Codex/GPT-5.6 Sol
for the formalization. This extension makes no first-proof or originality claim.
The private API below is deliberately pinned to the source module and commit.
Verification details are recorded in the accompanying README and verification.json.
-/
import ErdosProblems.Erdos511

-- Lean names contain a numeric component that cannot be entered as an ordinary
-- identifier. This macro emits that existing constant name; it adds no axioms.
macro:max "source511% " n:ident : term =>
  pure (Lean.mkIdent
    (((Lean.Name.num `_private.ErdosProblems.Erdos511 0).str "Erdos511").append n.getId))

macro "unfold511" "[" ns:ident,* "]" : tactic => do
  let ids := ns.getElems.map fun n => Lean.mkIdent
    (((Lean.Name.num `_private.ErdosProblems.Erdos511 0).str "Erdos511").append n.getId)
  `(tactic| unfold $[$ids:ident]*)

open Polynomial Set Topology Metric

namespace JSP410Closed
noncomputable section

def closedLemniscate (p : Polynomial ℂ) : Set ℂ := {z | ‖p.eval z‖ ≤ 1}

def HasLargeClosedComponents (p : Polynomial ℂ) (d : ℝ) (N : ℕ) : Prop :=
  ∃ C : Fin N → Set ℂ, Function.Injective C ∧
    ∀ i, C i ∈ Erdos511.componentsIn (closedLemniscate p) ∧ d < Metric.diam (C i)

/-- A continuous barrier excludes its level-one boundary from a component. -/
private lemma component_stays_below_barrier
    (s : Set ℂ) (b : ℂ) (g : ℂ → ℝ) (hg : Continuous g)
    (hb : b ∈ s) (hgb : g b < 1)
    (hboundary : ∀ z, g z = 1 → z ∉ s) :
    connectedComponentIn s b ⊆ {z | g z < 1} := by
  intro z hz
  by_contra h
  have interval : (1 : ℝ) ∈ Icc (g b) (g z) := ⟨hgb.le, le_of_not_gt h⟩
  obtain ⟨w, hw, hwg⟩ := isPreconnected_connectedComponentIn.intermediate_value
    (mem_connectedComponentIn hb) hz hg.continuousOn interval
  exact hboundary w hwg (connectedComponentIn_subset s b hw)

/-- The upstream strict barrier also separates components of the closed sublevel set. -/
theorem arbitrarily_many_large_closed_components (N : ℕ) :
    ∃ p : Polynomial ℂ, p.Monic ∧ HasLargeClosedComponents p (6 / 5 : ℝ) N := by
  classical
  obtain ⟨p, monic, approx⟩ := (source511% exists_monic_approx_target) N
  let b : Fin N → ℂ := fun i => (source511% mkPoint) 0 ((source511% centerHeight) N i)
  let g : Fin N → ℂ → ℝ := fun i => (source511% boxGauge) N i
  let C : Fin N → Set ℂ := fun i => connectedComponentIn (closedLemniscate p) (b i)
  have core (i : Fin N) : (source511% coreSegment) N i ⊆ closedLemniscate p := by
    intro z hz
    have strict : ‖p.eval z‖ < 1 := (source511% coreSegment_subset_lemniscate) N p approx i hz
    exact strict.le
  have center (i : Fin N) : b i ∈ closedLemniscate p :=
    core i ((source511% center_mem_coreSegment) N i)
  have boundary (i : Fin N) (z : ℂ) (hz : g i z = 1) : z ∉ closedLemniscate p := by
    have ball := (source511% boxGauge_le_one_mem_closedBall) N i hz.le
    have err := approx z (by simpa only [Metric.mem_closedBall, dist_zero_right] using ball)
    have lower := (source511% target_norm_ge_one_add_barrierMargin_on_boxGauge_eq_one) N i hz
    have triangle : ‖(source511% target) N z‖ ≤
        ‖p.eval z - (source511% target) N z‖ + ‖p.eval z‖ := by
      simpa only [sub_add_cancel, norm_sub_rev] using
        norm_add_le ((source511% target) N z - p.eval z) (p.eval z)
    change ¬ ‖p.eval z‖ ≤ 1
    linarith [(source511% barrierMargin_pos) N]
  have trap (i : Fin N) : C i ⊆ {z | g i z < 1} := by
    apply component_stays_below_barrier (closedLemniscate p) (b i) (g i)
      ((source511% continuous_boxGauge) N i) (center i)
    · change (source511% boxGauge) N i
        ((source511% mkPoint) 0 ((source511% centerHeight) N i)) < 1
      unfold511 [boxGauge, mkPoint, outerHalfLength]
      simp
    · exact boundary i
  have injective : Function.Injective C := by
    intro i j equal
    by_contra different
    have mem : b j ∈ C i := by
      rw [equal]
      exact mem_connectedComponentIn (center j)
    exact (source511% center_not_mem_other_openBox) N different (trap i mem)
  refine ⟨p, monic, C, injective, fun i => ⟨?_, ?_⟩⟩
  · exact ⟨⟨b i, center i⟩, connectedComponentIn_eq_image (center i)⟩
  · have inside : (source511% coreSegment) N i ⊆ C i :=
      ((source511% isPreconnected_coreSegment) N i).subset_connectedComponentIn
        ((source511% center_mem_coreSegment) N i) (core i)
    let left := (source511% mkPoint) (-(source511% innerHalfLength))
      ((source511% centerHeight) N i)
    let right := (source511% mkPoint) (source511% innerHalfLength)
      ((source511% centerHeight) N i)
    have hl : left ∈ C i := inside ⟨-(source511% innerHalfLength), by
      unfold511 [innerHalfLength]
      norm_num, rfl⟩
    have hr : right ∈ C i := inside ⟨(source511% innerHalfLength), by
      unfold511 [innerHalfLength]
      norm_num, rfl⟩
    have bounded : Bornology.IsBounded (C i) :=
      Metric.isBounded_closedBall.subset (fun z hz =>
        (source511% boxGauge_le_one_mem_closedBall) N i (trap i hz).le)
    have distance : dist left right = (5 / 4 : ℝ) := by
      dsimp only [left, right]
      unfold511 [mkPoint, innerHalfLength]
      norm_num [Complex.dist_eq, Complex.norm_def, Complex.normSq]
    have diameter := Metric.dist_le_diam_of_mem bounded hl hr
    rw [distance] at diameter
    linarith

/-- No degree-independent bound exists for closed components above every threshold d>1. -/
theorem not_uniformly_bounded_closed_components :
    ¬ (∀ d : ℝ, 1 < d → ∃ B : ℕ, ∀ p : Polynomial ℂ, p.Monic →
      ¬ HasLargeClosedComponents p d (B + 1)) := by
  intro bound
  obtain ⟨B, impossible⟩ := bound (6 / 5) (by norm_num)
  obtain ⟨p, hp, hc⟩ := arbitrarily_many_large_closed_components (B + 1)
  exact impossible p hp hc

#print axioms arbitrarily_many_large_closed_components
#print axioms not_uniformly_bounded_closed_components

end
end JSP410Closed



