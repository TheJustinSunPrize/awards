import ErdosProblems.Erdos1064

namespace JSP000884

open Filter
open scoped Nat

/-- The exact conjunction of the three source formalizations used for Erdős Problem 1064. -/
def target : Prop :=
  {n | Nat.totient n > Nat.totient (n - Nat.totient n)}.HasDensity 1 ∧
    {n | Nat.totient n < Nat.totient (n - Nat.totient n)}.Infinite ∧
      ∀ f : ℕ → ℕ,
        (fun n : ℕ => (f n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) →
          {n | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}.HasDensity 1

/-- The imported proof closes the density and infinitude statements and
its stronger little-o perturbation variant. -/
theorem solution : target := by
  refine ⟨Erdos1064.erdos_1064, Erdos1064.erdos_1064.variants.k2, ?_⟩
  intro f hf
  exact Erdos1064.erdos_1064.variants.general_function f hf

end JSP000884
