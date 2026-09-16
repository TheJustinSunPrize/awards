import FivePointExact
import SendovSixPointPlane

/-! Exact values for N=5 and 6<=N<=8. Upper constructions are the
separately attributed, pinned work by superpilot69 and contributors.
The general classification remains open in this submission. -/
namespace JSP404
open Real

theorem guaranteed_two_pi_div_three {N : ℕ} (hN : 6 ≤ N) :
    Guaranteed N (2*π/3) := by
  intro s hs
  exact SendovSixPointPlane.finite_set_large_angle s (by omega)

theorem alpha_eq_two_pi_div_three {N : ℕ} (hlo : 6 ≤ N) (hhi : N ≤ 8) :
    alpha N = 2*π/3 := by
  apply le_antisymm
  · have hh := alpha_le_szekeres_upper (N := N) (k := 3)
      (by omega) (by omega) (by norm_num; exact hhi)
    norm_num at hh
    linarith
  · exact le_alpha (guaranteed_two_pi_div_three hlo)

theorem small_cases_exact :
    alpha 5 = 3*π/5 ∧ ∀ N : ℕ, 6 ≤ N → N ≤ 8 → alpha N = 2*π/3 :=
  ⟨alpha_five_eq_three_pi_div_five, fun _ hlo hhi => alpha_eq_two_pi_div_three hlo hhi⟩

#print axioms small_cases_exact
#print axioms guaranteed_two_pi_div_three
#print axioms alpha_eq_two_pi_div_three
end JSP404

