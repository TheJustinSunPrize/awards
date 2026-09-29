/-
Audit file for JSP-000301.

It re-states the main results with their types (so a reviewer can see the exact
statements), and prints the axioms each theorem depends on.  A clean run shows
only Lean/Mathlib's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), with no placeholder axiom of any kind, i.e. no gaps.
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

/-- Typed restatement of the existential form (definitional check). -/
theorem exists_restated :
    ∃ a b : ℕ, 0 < a ∧ IsPowerful a ∧ IsPowerful b ∧ b = a + 1 ∧
      ¬ IsSquare a ∧ ¬ IsSquare b :=
  jsp_000301_exists

#print axioms JSP000301.powerful_12167
#print axioms JSP000301.powerful_12168
#print axioms JSP000301.not_isSquare_of_between
#print axioms JSP000301.not_isSquare_12167
#print axioms JSP000301.not_isSquare_12168
#print axioms JSP000301.jsp_000301_witness
#print axioms JSP000301.jsp_000301
#print axioms JSP000301.jsp_000301_exists
#print axioms witness_restated
#print axioms main_restated
#print axioms exists_restated
