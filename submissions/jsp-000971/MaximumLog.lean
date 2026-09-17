import RandomWalkCover
import LogTailNumerics
import ProbabilityAssembly
import ErdosProblems.Erdos1165.HLOZFixedPointLocalTimeTail

namespace JSP000971
open Filter MeasureTheory Erdos1165
open scoped ENNReal Topology

/-- Summable maximum tail for the actual planar simple random walk law. -/
theorem maximum_threshold_tail (n : ℕ) :
    simpleRandomWalk {s | returnThreshold n ≤ maximum s n} ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    simpa using (prob_le_one (μ := simpleRandomWalk)
      (s := {s | returnThreshold 0 ≤ maximum s 0}))
  have hn1 : 1 ≤ n := by omega
  have horigin := HLOZFixedPointLocalTimeTail.simpleRandomWalk_originLocalTimeEvent_le
    hn1 (returnThreshold_ge_two n hn1)
  simp only [HLOZFixedPointLocalTimeTail.originLocalTimeEvent,
    Bridge.localTime_eq, Gap.geometricReturnCost, Nat.cast_add, Nat.cast_one] at horigin
  exact (maximum_tail_le_origin n (returnThreshold n)).trans
    ((mul_le_mul_right horigin (n + 1 : ℝ≥0∞)).trans
      (geometric_maximum_tail_bound n hn1))

/-- The maximum local time is eventually at most 2000 log² n almost surely.
The start time may depend on the path; the constant is deterministic. -/
theorem ae_maximum_le_log_sq :
    ∀ᵐ s ∂simpleRandomWalk, ∃ N : ℕ, ∀ n, N ≤ n →
      (maximum s n : ℝ) ≤ 2000 * (Real.log (n : ℝ)) ^ 2 := by
  have hsum : (∑' n : ℕ,
      simpleRandomWalk {s | returnThreshold n ≤ maximum s n}) ≠ ∞ :=
    ne_top_of_le_ne_top summable_inverse_square_succ.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum maximum_threshold_tail)
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with s hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  refine ⟨max N 2, ?_⟩
  intro n hn
  apply below_returnThreshold_log_bound n (maximum s n)
    ((le_max_right N 2).trans hn)
  exact lt_of_not_ge (hN n ((le_max_left N 2).trans hn))

theorem ae_maximumLogBound :
    ∀ᵐ s ∂simpleRandomWalk, MaximumLogBound s := by
  filter_upwards [ae_maximum_le_log_sq] with s hs
  exact ⟨2000, by norm_num, hs⟩

#print axioms maximum_threshold_tail
#print axioms ae_maximum_le_log_sq
#print axioms ae_maximumLogBound
end JSP000971
