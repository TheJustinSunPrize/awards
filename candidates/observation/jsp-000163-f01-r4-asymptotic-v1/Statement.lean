import Mathlib
import ErdosProblems.Erdos166

set_option autoImplicit false

open Filter Real

namespace JSP000163

/-- The frozen JSP-000163 catalog statement, expressed as the positive
answer to the cited off-diagonal Ramsey asymptotic question. -/
def targetStatement : Prop :=
  ∃ c : ℕ, 0 < c ∧
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ ↦ (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ c)
      (fun k : ℕ ↦ (Ramsey.ramseyNumber 4 k : ℝ))

end JSP000163
