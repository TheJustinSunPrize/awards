import JSP331.Correspondence
import ErdosProblems.Erdos402

/-!
Statement bridge to the existing proof published in plby/lean-proofs.
The mathematical proof and its formalization are upstream work; see REFERENCES.md.
-/

namespace JSP331

/-- JSP-000331's eventual inequality, by the pinned upstream formalization. -/
theorem eventual_graham : EventualGrahamStatement := by
  exact Erdos402.erdos_402

/-- An expanded interface exposing every hypothesis and the rational conclusion. -/
theorem sufficiently_large_gcd_bound :
    ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → 0 ∉ A → A.Nonempty →
      ∃ a ∈ A, ∃ b ∈ A, (a.gcd b : ℚ) ≤ (a : ℚ) / A.card :=
  eventual_graham

/-- The eventual result supplies distinct members after raising the threshold to two. -/
theorem sufficiently_large_distinct_gcd_bound :
    ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → 0 ∉ A → A.Nonempty →
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ (a.gcd b : ℚ) ≤ (a : ℚ) / A.card := by
  obtain ⟨N, hN⟩ := eventual_graham
  refine ⟨max N 2, ?_⟩
  intro A hcard hzero hnonempty
  obtain ⟨a, ha, b, hb, hbound⟩ :=
    hN A ((le_max_left N 2).trans hcard) hzero hnonempty
  exact ⟨a, ha, b, hb,
    distinct_of_gcd_bound hzero ((le_max_right N 2).trans hcard) ha hbound, hbound⟩

end JSP331
