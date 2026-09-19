import SendovFivePointPlane
import JSP404.ThreeClusterGeometry

/-! Combine our five-point lower bound with the separately attributed,
pinned upper construction by superpilot69 and contributors (PR #42).
This closes only N=5; it is not the general Sendov classification. -/
namespace JSP404
open Real

theorem guaranteed_five_three_pi_div_five : Guaranteed 5 (3*π/5) := by
  intro s hs
  exact SendovFivePointPlane.finite_set_large_angle s (by omega)

theorem alpha_five_eq_three_pi_div_five : alpha 5 = 3*π/5 := by
  apply le_antisymm alpha_five_le_three_pi_div_five
  exact le_alpha guaranteed_five_three_pi_div_five

#print axioms guaranteed_five_three_pi_div_five
#print axioms alpha_five_eq_three_pi_div_five
end JSP404
