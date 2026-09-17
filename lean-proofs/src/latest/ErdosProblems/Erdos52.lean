/-!
# Erdős Problem 52: Consecutive Integers with Equal Divisor Counts

This is a Lean formalization of the solution to Erdős Problem 52.
https://www.erdosproblems.com/forum/thread/52

Erdős Problem 52: Are there infinitely many consecutive integers
with equal divisor counts?
Answer: Yes.

Informal authors:
- P. Erdős and C. Pomerance (original proof, 1952)

Formal author:
- OpenAI Codex

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos52.md
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

import ErdosProblems.Erdos52.Basic

namespace Erdos52

/-- There exist infinitely many consecutive integers with equal divisor counts. -/
theorem exists_infinitely_many_consecutive_equal_d :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ d n = d (n + 1) :=
  Erdos52.Basic.exists_infinitely_many_consecutive_equal_d

end Erdos52
