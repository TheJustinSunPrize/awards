import JSP692.AlonGrowth
import JSP692.LinearIntersection

set_option autoImplicit false

/-!
Both questions of JSP-000692 / Erdős 836 in one final theorem.
Question 1 counts support H (the union of all edges), never a padded ambient set.
The counterexamples additionally satisfy support H = univ.
Question 2 requires DISTINCT edges and a single positive real constant.
-/

namespace JSP692

/-- A putative eventual quadratic bound, uniform over all eligible hypergraphs. -/
def QuadraticVertexBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ,
    ∀ r : ℕ, 2 ≤ r → R ≤ r →
    ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
      Uniform H r → ThreeChromatic H → Intersecting H →
      ((support H).card : ℝ) ≤ C * (r : ℝ) ^ 2

/-- The linear-intersection assertion, with the constant outside all other
quantifiers and the distinctness condition explicit. -/
def LinearIntersectionAssertion : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ r : ℕ, 2 ≤ r →
    ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
      Uniform H r → ThreeChromatic H → Intersecting H →
      ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
        C * (r : ℝ) ≤ ((e ∩ f).card : ℝ)

/-- Arbitrarily high-rank counterexamples to every quadratic coefficient.
This is stronger than a single witness with more than r^2 ambient vertices. -/
theorem quadratic_counterexamples (C : ℝ) (R : ℕ) :
    ∃ r : ℕ, 2 ≤ r ∧ R ≤ r ∧
      ∃ n : ℕ, ∃ H : Hypergraph (Fin n),
        Uniform H r ∧ ThreeChromatic H ∧ Intersecting H ∧
        support H = Finset.univ ∧
        C * (r : ℝ) ^ 2 < ((support H).card : ℝ) := by
  obtain ⟨m, hmR, hbig⟩ := alon_exceeds_every_quadratic C R
  exact ⟨m + 2, by omega, hmR, Fintype.card (AlonVertex m), alonFin m,
    alonFin_uniform m, alonFin_threeChromatic m, alonFin_intersecting m,
    alonFin_support_eq_univ m, hbig⟩

/-- Question 1: NO, even when isolated vertices are forbidden. -/
theorem jsp000692_question_one : ¬ QuadraticVertexBound := by
  rintro ⟨C, _hC, R, hbound⟩
  obtain ⟨r, hr, hR, n, H, hu, hc, hi, _hfull, hbig⟩ :=
    quadratic_counterexamples C R
  exact (not_le_of_gt hbig) (hbound r hr hR n H hu hc hi)

/-- Question 2: YES, with the explicit universal constant 1/3. -/
theorem jsp000692_question_two_assertion : LinearIntersectionAssertion :=
  jsp000692_question_two

/-- The complete pair of answers, on the SAME definitions of eligible
hypergraph, colourability, active vertices, and edge intersection. -/
theorem jsp000692_complete : ¬ QuadraticVertexBound ∧ LinearIntersectionAssertion :=
  ⟨jsp000692_question_one, jsp000692_question_two_assertion⟩

/-- Fully expanded alternative final theorem for statement-to-problem review. -/
theorem jsp000692_complete_explicit :
    (∀ C : ℝ, ∀ R : ℕ,
      ∃ r : ℕ, 2 ≤ r ∧ R ≤ r ∧
        ∃ n : ℕ, ∃ H : Hypergraph (Fin n),
          Uniform H r ∧ ThreeChromatic H ∧ Intersecting H ∧
          support H = Finset.univ ∧
          C * (r : ℝ) ^ 2 < ((support H).card : ℝ)) ∧
    (∀ r : ℕ, 2 ≤ r →
      ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
        Uniform H r → ThreeChromatic H → Intersecting H →
        ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
          (r : ℝ) / 3 ≤ ((e ∩ f).card : ℝ)) := by
  constructor
  · exact quadratic_counterexamples
  · intro r hr n H hu hc hi
    exact large_intersection_one_third hr hu hi hc.2

end JSP692
