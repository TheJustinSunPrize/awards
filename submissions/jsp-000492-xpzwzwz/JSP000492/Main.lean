import JSP000492.Construction
import JSP000492.Pairs
import JSP000492.Padding
import JSP000492.Scale

namespace JSP000492

/-- At every prescribed size, pad the grid without losing equal-distance pairs. -/
theorem configuration_every_size (n : ℕ) :
    ∃ S : Finset E, S.card = n ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
      gridSize n ^ 4 ≤ pairCount S := by
  obtain ⟨S, hcard, hsphere, D, hDcard, hDmem, hDrev⟩ := sphere_grid (gridSize n)
  obtain ⟨T, hST, hTcard, hTsphere⟩ := pad_finite_set unitSphere_infinite S hsphere n
    (by rw [hcard]; exact gridSize_fits n)
  refine ⟨T, hTcard, hTsphere, ?_⟩
  calc
    gridSize n ^ 4 = D.card := hDcard.symm
    _ ≤ pairCount S := card_le_pairCount S D hDmem hDrev
    _ ≤ pairCount T := pairCount_mono hST

/-- Quantitative uniform version: every sufficiently large size beats `K` pairs per vertex. -/
theorem eventually_many_pairs (K n : ℕ) (hn : 3 * (24 * K + 1) ^ 3 ≤ n) :
    ∃ S : Finset E, S.card = n ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
      K * n ≤ pairCount S := by
  obtain ⟨S, hcard, hsphere, hcount⟩ := configuration_every_size n
  exact ⟨S, hcard, hsphere, (gridSize_many K n hn).trans hcount⟩

/-- The original existence-of-a-diverging-function question, with fixed sphere and distance.
`pairCount` counts unordered distinct pairs at Euclidean distance `sqrt 2`. -/
theorem erdos605 :
    ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, ∃ S : Finset E, S.card = n ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
        (n : ℝ) * f n ≤ (pairCount S : ℝ) := by
  refine ⟨fun n => (quota n : ℝ), quota_real_tendsto, ?_⟩
  intro n
  obtain ⟨S, hcard, hsphere, hcount⟩ := configuration_every_size n
  refine ⟨S, hcard, hsphere, ?_⟩
  have h : quota n * n ≤ pairCount S := (quota_many n).trans hcount
  change (n : ℝ) * (quota n : ℝ) ≤ (pairCount S : ℝ)
  exact_mod_cast (show n * quota n ≤ pairCount S by simpa [Nat.mul_comm] using h)

end JSP000492
