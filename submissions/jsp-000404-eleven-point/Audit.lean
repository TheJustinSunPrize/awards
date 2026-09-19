import SunPrize.ElevenGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! 通过新声明触发总定理的内核复核，并输出其实际公理依赖。 -/
namespace SunPrize.Audit

theorem angle_statement (s : Finset (EuclideanSpace ℝ (Fin 2))) (hs : 11 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 3 * Real.pi / 4 ≤ EuclideanGeometry.angle a b c :=
  eleven_point_angle s hs

theorem value_statement {n : ℕ} (hn : 11 ≤ n) (hn' : n ≤ 16) :
    JSP404.alpha n = 3 * Real.pi / 4 :=
  alpha_eleven_to_sixteen hn hn'

#check @angle_statement
#check @value_statement
#print axioms angle_statement
#print axioms value_statement
end SunPrize.Audit
