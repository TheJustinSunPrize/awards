import SunPrize.Certificate.LogicClosure
import SunPrize.Certificate.InputsValid
namespace SunPrize
/-- 十一点方向模型的组合下界。 -/
theorem eleven_point_direction_bound : ElevenPointDirectionBound := by
  intro t m
  by_contra h
  have ht : t < 4 := lt_of_not_ge h
  exact ElevenLogic.certificate_unsat (SMT.meaning t m) (SMT.inputs_valid t m ht)
#print axioms eleven_point_direction_bound
end SunPrize
