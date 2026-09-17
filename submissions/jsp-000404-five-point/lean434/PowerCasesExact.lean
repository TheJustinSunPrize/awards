import SendovStrictPower
import JSP404.ClassicalBounds

/-! Exact power-of-two thresholds. This formalizes a classical subfamily,
not the complete Sendov classification. The upper construction is the
separately attributed pinned work by superpilot69 and contributors. -/
namespace JSP404
open Real

/-- Every set with at least 2^n points has an angle at least (1-1/n)*pi. -/
theorem guaranteed_power_threshold {N n : ℕ} (hn : 2 ≤ n) (hN : 2^n ≤ N) :
    Guaranteed N ((1-1/(n : ℝ))*π) := by
  intro s hs
  have hs3 : 3 ≤ s.card := by rw [hs]; exact (three_le_two_pow hn).trans hN
  apply (hasLargeAngle_iff_le_maxAngle hs3).mpr
  by_contra h
  have hM : maxAngle s < (1-1/(n : ℝ))*π := lt_of_not_ge h
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htarget : (1-1/(n : ℝ))*π < π := by
    have hh := mul_pos (one_div_pos.mpr hnreal) pi_pos
    nlinarith
  have hlam : 0 < π-maxAngle s := by linarith
  have ht : π/(π-maxAngle s) < (n : ℝ) := by
    apply (div_lt_iff₀ hlam).mpr
    have hh := mul_lt_mul_of_pos_right hM hnreal
    have hne := ne_of_gt hnreal
    field_simp at hh
    nlinarith
  obtain ⟨m⟩ := SendovDirectionModel.model_of_finite_set s hlam (by
    intro a ha b hb c hc hab hac hbc
    simpa using angle_le_maxAngle ha hb hc hab hac hbc)
  have hcard := SendovStrictPower.model_card_lt m (by omega) hn ht
  omega

/-- The classical equality for every power of two, including 4, 8, 16, ... . -/
theorem alpha_power_two_exact {n : ℕ} (hn : 2 ≤ n) :
    alpha (2^n) = (1-1/(n : ℝ))*π :=
  le_antisymm (szekeres_upper_bound n hn)
    (le_alpha (guaranteed_power_threshold hn le_rfl))

#print axioms guaranteed_power_threshold
#print axioms alpha_power_two_exact
end JSP404
