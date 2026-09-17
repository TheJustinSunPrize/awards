import Mathlib.Analysis.Asymptotics.Defs
import Counting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Conditional assembly only: the two probabilistic inputs are explicit theorem
parameters. This module does not assert them for simple random walk. -/
namespace JSP000971
open Filter MeasureTheory
open scoped ENNReal Topology

/-- The pathwise logarithmic conclusion, with constants and start time allowed
to depend on the path. -/
def HistoricalLogBound (s : ℕ → ℤ × ℤ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    ((historical s n).card : ℝ) ≤ C * (Real.log (n : ℝ)) ^ 2

def MaximumLogBound (s : ℕ → ℤ × ℤ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    (maximum s n : ℝ) ≤ C * (Real.log (n : ℝ)) ^ 2

lemma eventually_one_le_log_sq :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
  have h : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  nlinarith

/-- Both pathwise inputs are required; neither is introduced as an axiom. -/
theorem historicalLogBound_of_two_inputs (s : ℕ → ℤ × ℤ)
    (hf : ∃ N : ℕ, ∀ n, N ≤ n → (favorites s n).card ≤ 3)
    (hm : MaximumLogBound s) : HistoricalLogBound s := by
  obtain ⟨Nf, hf⟩ := hf
  obtain ⟨C, hC, Nm, hm⟩ := hm
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp eventually_one_le_log_sq
  refine ⟨(Nf : ℝ) + 3 * C, by positivity, max Nf (max Nm Nl), ?_⟩
  intro n hn
  have hnf : Nf ≤ n := (le_max_left _ _).trans hn
  have hnm : Nm ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hnl : Nl ≤ n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  have hc := historical_card_le s Nf n 3 (fun k hk _ => hf k hk)
  have hcr : ((historical s n).card : ℝ) ≤ (Nf : ℝ) + 3 * (maximum s n : ℝ) := by
    exact_mod_cast hc
  have hlog := hl n hnl
  have hm' := hm n hnm
  have hmul : (Nf : ℝ) ≤ (Nf : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
    le_mul_of_one_le_right (Nat.cast_nonneg Nf) hlog
  nlinarith

/-- Almost-sure assembly for any measure on planar paths. Probabilistic inputs
must still be supplied from proved theorems for that SAME measure. -/
theorem ae_historicalLogBound_of_two_inputs
    (μ : Measure (ℕ → ℤ × ℤ))
    (hf : ∀ᵐ s ∂μ, ∃ N : ℕ, ∀ n, N ≤ n → (favorites s n).card ≤ 3)
    (hm : ∀ᵐ s ∂μ, MaximumLogBound s) :
    ∀ᵐ s ∂μ, HistoricalLogBound s := by
  filter_upwards [hf, hm] with s hs ht
  exact historicalLogBound_of_two_inputs s hs ht

/-- A concrete summable exceedance bound is sufficient for the maximum
local-time input, by the first Borel-Cantelli lemma. -/
theorem ae_maximumLogBound_of_summable
    (μ : Measure (ℕ → ℤ × ℤ)) (C : ℝ) (hC : 0 ≤ C)
    (hsum : (∑' n : ℕ, μ {s | C * (Real.log (n : ℝ)) ^ 2 <
      (maximum s n : ℝ)}) ≠ ∞) :
    ∀ᵐ s ∂μ, MaximumLogBound s := by
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with s hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  refine ⟨C, hC, N, ?_⟩
  intro n hn
  exact le_of_not_gt (hN n hn)

theorem HistoricalLogBound.isBigO {s : ℕ → ℤ × ℤ} (h : HistoricalLogBound s) :
    (fun n : ℕ => ((historical s n).card : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log (n : ℝ)) ^ 2) := by
  obtain ⟨C, _, N, hN⟩ := h
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (historical s n).card),
    abs_of_nonneg (sq_nonneg (Real.log (n : ℝ)))] using hN n hn

#print axioms HistoricalLogBound.isBigO
#print axioms ae_maximumLogBound_of_summable
#print axioms historicalLogBound_of_two_inputs
#print axioms ae_historicalLogBound_of_two_inputs
end JSP000971
