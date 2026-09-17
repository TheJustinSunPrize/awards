import ErdosProblems.Erdos92

namespace JSP000108

open Filter

/-- The exact formal target used for the strong subpolynomial question in the
public Formal Conjectures source for JSP-000108. -/
def target_statement : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n in atTop,
    (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (c / (n : ℝ).log.log)

/-- The cited unit-distance counterexample proves that the target upper bound
is false. -/
theorem not_jsp_000108 : ¬ target_statement := by
  simpa only [target_statement] using Erdos92.erdos_92.variants.not_erdos_92

/-- Package the negative answer as a literal equivalence. -/
theorem answer_false_iff : False ↔ target_statement := by
  constructor
  · exact False.elim
  · intro h
    exact False.elim (not_jsp_000108 h)

#print axioms not_jsp_000108
#print axioms answer_false_iff

end JSP000108
