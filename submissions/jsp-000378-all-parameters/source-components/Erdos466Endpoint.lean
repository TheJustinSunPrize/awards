/-
Endpoint obstruction for Erdős 466 / JSP-000378.
The odd-distance obstruction is classical; see Graham, Rothschild and
Straus, "Are there n+2 points in E^n with odd integral distances?" (1974).
This file connects the elementary Gram-determinant calculation to the
standard Euclidean metric and the nearest-integer convention.
-/
import Erdos466Definitions
import Erdos466EndpointArithmetic

namespace Erdos466General
noncomputable section

lemma gram_distances_zero (p₀ p₁ p₂ p₃ : Plane) :
    sixDistanceGramDet
      (4 * dist p₀ p₁ ^ 2) (4 * dist p₀ p₂ ^ 2) (4 * dist p₀ p₃ ^ 2)
      (4 * dist p₁ p₂ ^ 2) (4 * dist p₁ p₃ ^ 2) (4 * dist p₂ p₃ ^ 2) = 0 := by
  simp only [plane_dist_sq, sixDistanceGramDet]
  ring

/-- Four planar points cannot have all six distances at least one half away
from the nearest integer. This treats the non-strict endpoint in the original problem. -/
theorem no_four_half (p₀ p₁ p₂ p₃ : Plane)
    (h₀₁ : 1 / 2 ≤ distToInt (dist p₀ p₁))
    (h₀₂ : 1 / 2 ≤ distToInt (dist p₀ p₂))
    (h₀₃ : 1 / 2 ≤ distToInt (dist p₀ p₃))
    (h₁₂ : 1 / 2 ≤ distToInt (dist p₁ p₂))
    (h₁₃ : 1 / 2 ≤ distToInt (dist p₁ p₃))
    (h₂₃ : 1 / 2 ≤ distToInt (dist p₂ p₃)) : False := by
  obtain ⟨a, ha⟩ := (half_le_distToInt_iff _).mp h₀₁
  obtain ⟨b, hb⟩ := (half_le_distToInt_iff _).mp h₀₂
  obtain ⟨c, hc⟩ := (half_le_distToInt_iff _).mp h₀₃
  obtain ⟨d, hd⟩ := (half_le_distToInt_iff _).mp h₁₂
  obtain ⟨e, he⟩ := (half_le_distToInt_iff _).mp h₁₃
  obtain ⟨f, hf⟩ := (half_le_distToInt_iff _).mp h₂₃
  have hsq (x : ℝ) (z : ℤ) (hz : 2 * x = (2 * z + 1 : ℤ)) :
      ((((2 * z + 1) ^ 2 : ℤ)) : ℝ) = 4 * x ^ 2 := by
    rw [Int.cast_pow, ← hz]
    ring
  have hzero :
      sixDistanceGramDet ((2*a+1)^2) ((2*b+1)^2) ((2*c+1)^2)
        ((2*d+1)^2) ((2*e+1)^2) ((2*f+1)^2) = (0 : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    rw [sixDistanceGramDet_intCast]
    rw [hsq _ _ ha, hsq _ _ hb, hsq _ _ hc, hsq _ _ hd, hsq _ _ he, hsq _ _ hf]
    simpa only [Int.cast_zero] using gram_distances_zero p₀ p₁ p₂ p₃
  have hodd (z : ℤ) : Odd (2 * z + 1) := ⟨z, by ring⟩
  exact sixDistanceGramDet_ne_zero_of_odd _ _ _ _ _ _
    (hodd a) (hodd b) (hodd c) (hodd d) (hodd e) (hodd f) hzero

theorem no_four_at_or_above_half {δ : ℝ} (hδ : 1 / 2 ≤ δ)
    (P : Fin 4 → Plane)
    (hP : ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))) : False := by
  exact no_four_half (P 0) (P 1) (P 2) (P 3)
    (hδ.trans (hP 0 1 (by decide))) (hδ.trans (hP 0 2 (by decide)))
    (hδ.trans (hP 0 3 (by decide))) (hδ.trans (hP 1 2 (by decide)))
    (hδ.trans (hP 1 3 (by decide))) (hδ.trans (hP 2 3 (by decide)))

end
end Erdos466General
