import Erdos1077

namespace JSP000660

open Filter SimpleGraph

open scoped Classical in
/-- The exact positive assertion recorded by Formal Conjectures for
Erdos Problem 1077 and used for JSP-000660. -/
def target_statement : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 →
    ∀ᶠ D in atTop, ∀ᶠ n in atTop,
      ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
        ∃ (H : Subgraph G),
          letI m := H.verts.ncard
          SimpleGraph.IsBalanced H.coe D ∧
            m > (n : ℝ) ^ (1 - α) ∧
            H.edgeSet.ncard > ε * m ^ (1 + α)

/-- JSP-000660 has the negative answer: the exact positive assertion is false. -/
theorem not_jsp_000660 : ¬ target_statement := by
  simpa only [target_statement] using Erdos1077.not_erdos_1077

/-- The negative answer is also packaged as the literal proposition
`False ↔ target_statement`, without depending on the Formal Conjectures API. -/
theorem answer_false_iff : False ↔ target_statement := by
  constructor
  · exact False.elim
  · intro h
    exact False.elim (not_jsp_000660 h)

#print axioms not_jsp_000660
#print axioms answer_false_iff

end JSP000660
