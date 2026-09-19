import SmallCasesExact
import PowerCasesExact

/-! Single audit target containing the verified small cases and the classical
power-of-two family. This does not assert the arbitrary-N classification. -/
namespace JSP404
open Real

theorem verified_cases_exact :
    (alpha 5 = 3*π/5 ∧ ∀ N : ℕ, 6 ≤ N → N ≤ 8 → alpha N = 2*π/3) ∧
    (∀ n : ℕ, 2 ≤ n → alpha (2^n) = (1-1/(n : ℝ))*π) :=
  ⟨small_cases_exact, fun _ hn => alpha_power_two_exact hn⟩

#print axioms verified_cases_exact
end JSP404
