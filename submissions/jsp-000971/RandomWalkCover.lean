import DefinitionBridge
import MaximumCover
import ErdosProblems.Erdos1165.Markov

namespace JSP000971
open MeasureTheory Erdos1165
open scoped ENNReal

lemma measurable_recenter (j : ℕ) : Measurable (recenter j) := by
  unfold recenter
  fun_prop

lemma randomWalk_map_recenter (j : ℕ) :
    simpleRandomWalk.map (recenter j) = simpleRandomWalk := by
  have hpath : recenter j ∘ trajectory = trajectory ∘ shiftSteps j := by
    funext w n
    exact trajectory_add_sub_trajectory w j n
  calc
    simpleRandomWalk.map (recenter j) = fairSteps.map (recenter j ∘ trajectory) := by
      rw [simpleRandomWalk, Measure.map_map (measurable_recenter j) measurable_trajectory]
    _ = fairSteps.map (trajectory ∘ shiftSteps j) := by rw [hpath]
    _ = (fairSteps.map (shiftSteps j)).map trajectory := by
      rw [Measure.map_map measurable_trajectory (measurable_shiftSteps j)]
    _ = simpleRandomWalk := by rw [fairSteps_map_shiftSteps]; rfl

lemma measurable_visits (n : ℕ) (x : ℤ × ℤ) :
    Measurable (fun s : WalkPath => visits s n x) := by
  have h : Measurable (fun s : WalkPath => localTime s n x) :=
    (measurable_of_countable (fun u : Fin (n + 1) → Point => localTimePrefix u x)).comp
      (measurable_pathPrefix n)
  simpa only [Bridge.localTime_eq] using h

/-- A genuine bound for planar simple random walk, requiring no unproved
probabilistic premise: reduce the maximum tail to n+1 origin tails. -/
theorem maximum_tail_le_origin (n k : ℕ) :
    simpleRandomWalk {s | k ≤ maximum s n} ≤
      (n + 1 : ℝ≥0∞) * simpleRandomWalk {s | k ≤ visits s n 0} := by
  let A : Set WalkPath := {s | k ≤ visits s n 0}
  have hA : MeasurableSet A := measurableSet_le measurable_const (measurable_visits n 0)
  have hshift : ∀ j, simpleRandomWalk (recenter j ⁻¹' A) = simpleRandomWalk A := by
    intro j
    rw [← Measure.map_apply_of_aemeasurable (measurable_recenter j).aemeasurable hA,
      randomWalk_map_recenter]
  have hcover : {s : WalkPath | k ≤ maximum s n} ⊆
      ⋃ j ∈ Finset.range (n + 1), recenter j ⁻¹' A := by
    intro s hs
    obtain ⟨j, hj, hmax⟩ := maximum_le_shifted_origin s n
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hs.trans hmax⟩⟩
  calc
    simpleRandomWalk {s | k ≤ maximum s n} ≤
        simpleRandomWalk (⋃ j ∈ Finset.range (n + 1), recenter j ⁻¹' A) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range (n + 1), simpleRandomWalk (recenter j ⁻¹' A) :=
      measure_biUnion_finset_le _ _
    _ = (n + 1 : ℝ≥0∞) * simpleRandomWalk A := by simp [hshift, nsmul_eq_mul]

#print axioms maximum_tail_le_origin
end JSP000971
