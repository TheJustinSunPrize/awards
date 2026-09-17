/-
Audit file for JSP-000301.

It re-states the main results with their types (so a reviewer can see the exact
statements), and prints the axioms each theorem depends on.  A clean run shows
only Lean/Mathlib's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and no `sorryAx`, i.e. no gaps in the proof.
-/
import Main

open JSP000301

/-- Typed restatement of the witness (definitional check). -/
theorem witness_restated :
    IsPowerful 12167 ∧ IsPowerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 :=
  jsp_000301_witness

/-- Typed restatement of the main theorem (definitional check). -/
theorem main_restated :
    ¬ (∀ n : ℕ, 0 < n → IsPowerful n → IsPowerful (n + 1) →
        IsSquare n ∨ IsSquare (n + 1)) :=
  jsp_000301

#print axioms JSP000301.powerful_12167
#print axioms JSP000301.powerful_12168
#print axioms JSP000301.not_isSquare_of_between
#print axioms JSP000301.not_isSquare_12167
#print axioms JSP000301.not_isSquare_12168
#print axioms JSP000301.jsp_000301_witness
#print axioms JSP000301.jsp_000301
