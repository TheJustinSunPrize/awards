import SunPrize.ElevenModel
import SendovDirectionModel
import JSP404.ClassicalBounds

/-!
十一点下界与十一至十六点的极值。
几何归约和二进制构造沿用 vendor/来源说明.md 中的既有形式化。
-/
namespace SunPrize
open Real JSP404

/-- 将既有几何归约的模型送入本项目已核查的同一组方向约束。 -/
def fromGeometricModel {n : ℕ} {t : ℝ} (m : SendovDirectionModel.Model n t) :
    DirectionModel n t where
  theta := m.theta
  range := m.range
  triangle i j k hij hjk := m.triangle i j k hij hjk

/-- 十一个不同的真实平面点必形成至少 135 度的角。 -/
theorem guaranteed_eleven : Guaranteed 11 (3 * π / 4) := by
  intro s hs
  have hs3 : 3 ≤ s.card := by omega
  apply (hasLargeAngle_iff_le_maxAngle hs3).mpr
  by_contra h
  have hM : maxAngle s < 3 * π / 4 := lt_of_not_ge h
  have hlam : 0 < π - maxAngle s := by linarith [pi_pos]
  have ht : π / (π - maxAngle s) < 4 := by
    apply (div_lt_iff₀ hlam).mpr
    nlinarith
  have models : Nonempty (SendovDirectionModel.Model 11 (π / (π - maxAngle s))) := by
    have bound := SendovDirectionModel.model_of_finite_set s hlam (by
      intro a ha b hb c hc hab hac hbc
      simpa using angle_le_maxAngle ha hb hc hab hac hbc)
    simpa [hs] using bound
  obtain ⟨m⟩ := models
  exact (not_lt_of_ge (eleven_point_direction_bound _ (fromGeometricModel m))) ht

/-- 对至少十一个点，直接给出所需的三个不同点。 -/
theorem eleven_point_angle (s : Finset (EuclideanSpace ℝ (Fin 2))) (hs : 11 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 3 * π / 4 ≤ EuclideanGeometry.angle a b c :=
  (guaranteed_mono hs guaranteed_eleven) s rfl

/-- 在十一至十六点范围内，极值阈值为 135 度。 -/
theorem alpha_eleven_to_sixteen {n : ℕ} (hn : 11 ≤ n) (hn' : n ≤ 16) :
    alpha n = 3 * π / 4 := by
  apply le_antisymm
  · have hu := alpha_le_szekeres_upper (N := n) (k := 4)
      (by omega) (by omega) (by norm_num; exact hn')
    norm_num at hu
    linarith
  · exact le_alpha (guaranteed_mono hn guaranteed_eleven)

#print axioms guaranteed_eleven
#print axioms eleven_point_angle
#print axioms alpha_eleven_to_sixteen
end SunPrize
