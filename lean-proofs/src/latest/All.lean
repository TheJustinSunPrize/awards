import ErdosProblems.Erdos307

/-!
# Erdős Problems

This file collects all Lean formalizations of solutions to Erdős problems.
-/

namespace ErdosProblems

/-- Formalization of Erdős Problem 307. -/
theorem erdos_307 : ∃ n : ℕ, 1 < n ∧ lpf n > lpf (n + 1) ∧ lpf (n + 1) > lpf (n + 2) :=
  Erdos307.exists_three_consecutive_decreasing_lpf

end ErdosProblems
