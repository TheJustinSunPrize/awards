import MaximumLog
import ErdosProblems.Erdos1165.AsymmetricCoarseRadialCompletionFamily
import ErdosProblems.Erdos1165.HLOZDirectSourceFinalAssembly
import ErdosProblems.Erdos1165.HLOZStructuralPastAdditiveRecurrence

/-! Connect the two unconditional almost-sure inputs to the independent
historical-favorites counting theorem, for precisely the same path measure. -/
namespace JSP000971
open Filter MeasureTheory Erdos1165

/-- Almost surely, eventually all favorite sets have at most three members. -/
theorem ae_eventually_favorites_card_le_three :
    ∀ᵐ s ∂simpleRandomWalk, ∃ N : ℕ, ∀ n, N ≤ n →
      (favorites s n).card ≤ 3 := by
  have hmax := HLOZDirectSourceFinalAssembly.hasPlanarMaximumLowerDeviation_of_asymmetricPairSource
    (fun delta _ => AsymmetricCoarseRadialCompletionFamily.eventually_nonempty_asymmetricPairSourceData delta)
  have hf := HLOZStructuralPastAdditiveRecurrence.simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_lowerDeviation hmax
  filter_upwards [hf] with s hs
  simpa only [Bridge.favoriteCount_eq] using (eventually_atTop.mp hs)

/-- Unconditional logarithmic-square bound on the number of distinct sites
that have ever been favorites, for planar simple symmetric random walk. -/
theorem ae_historicalLogBound :
    ∀ᵐ s ∂simpleRandomWalk, HistoricalLogBound s :=
  ae_historicalLogBound_of_two_inputs simpleRandomWalk
    ae_eventually_favorites_card_le_three ae_maximumLogBound

/-- The same conclusion in Mathlib's standard asymptotic notation. -/
theorem ae_historical_card_isBigO :
    ∀ᵐ s ∂simpleRandomWalk,
      (fun n : ℕ => ((historical s n).card : ℝ)) =O[atTop]
        (fun n : ℕ => (Real.log (n : ℝ)) ^ 2) :=
  ae_historicalLogBound.mono (fun _ h => h.isBigO)

/-- Explicit positive-constant form of the original asymptotic conclusion. -/
theorem erdos_1166 :
    ∀ᵐ s ∂simpleRandomWalk, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ((historical s n).card : ℝ) ≤ C * (Real.log (n : ℝ)) ^ 2 := by
  filter_upwards [ae_historicalLogBound] with s hs
  obtain ⟨C, hC, N, hN⟩ := hs
  refine ⟨C + 1, by linarith, N, ?_⟩
  intro n hn
  exact (hN n hn).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

#print axioms erdos_1166
#print axioms ae_historical_card_isBigO
#print axioms ae_eventually_favorites_card_le_three
#print axioms ae_historicalLogBound
end JSP000971
