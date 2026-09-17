/-!
# Erdős Problem 307: Three Consecutive Integers with Decreasing Largest Prime Factors

This is a Lean formalization of the solution to Erdős Problem 307.
https://www.erdosproblems.com/forum/thread/307

Erdős Problem 307: Can three consecutive integers have strictly decreasing largest prime factors?
Answer: Yes. For example, n = 13 gives P(13) = 13 > P(14) = 7 > P(15) = 5.

Informal authors:
- P. Erdős and C. Pomerance (original proof, 1978)

Formal authors:
- OpenAI Codex

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos307.md
-/

import Mathlib.NumberTheory.Prime
import Mathlib.Tactic

import ErdosProblems.Erdos307.Basic

namespace Erdos307

/-- There exist three consecutive integers with strictly decreasing largest prime factors. -/
theorem exists_three_consecutive_decreasing_lpf :
    ∃ n : ℕ, 1 < n ∧ lpf n > lpf (n + 1) ∧ lpf (n + 1) > lpf (n + 2) :=
  Erdos307.Basic.exists_three_consecutive_decreasing_lpf

end Erdos307
