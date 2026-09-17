import NineModelTrial
import JSP404.ThreeClusterGeometry

/-! Exact nine- and ten-point values; this does not prove the full classification. -/
namespace JSP404
open Real

theorem guaranteed_nine_five_pi_sevenths : Guaranteed 9 (5*π/7) := by
  intro s hs
  have hs3 : 3 ≤ s.card := by omega
  apply (hasLargeAngle_iff_le_maxAngle hs3).mpr
  by_contra h
  have hM : maxAngle s < 5*π/7 := lt_of_not_ge h
  have hlam : 0 < π-maxAngle s := by linarith [pi_pos]
  have ht : π/(π-maxAngle s) < (7:ℝ)/2 := by
    apply (div_lt_iff₀ hlam).mpr
    nlinarith
  have models : Nonempty (SendovDirectionModel.Model 9 (π/(π-maxAngle s))) := by
    have hh := SendovDirectionModel.model_of_finite_set s hlam (by
      intro a ha b hb c hc hab hac hbc
      simpa using angle_le_maxAngle ha hb hc hab hac hbc)
    simpa [hs] using hh
  obtain ⟨m⟩ := models
  exact (not_lt_of_ge (NineModelTrial.model_nine_lower m)) ht

theorem alpha_nine_ten_exact {N : ℕ} (hlo : 9 ≤ N) (hhi : N ≤ 10) :
    alpha N = 5*π/7 := by
  apply le_antisymm
  · have hu := alpha_le_sendov_intermediate_upper (N := N) (n := 3)
      (by omega) (by omega) (by norm_num; exact hhi)
    norm_num at hu
    linarith
  · exact le_alpha (guaranteed_mono hlo guaranteed_nine_five_pi_sevenths)

#print axioms guaranteed_nine_five_pi_sevenths
#print axioms alpha_nine_ten_exact
end JSP404
