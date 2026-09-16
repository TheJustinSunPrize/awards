import KorskyInject
import Mathlib.Data.Fintype.Powerset

/-!
Two checked counterexamples guard essential hypotheses. These are proofs of
negations, so the negative controls themselves are expected to compile.
They use kernel `decide`, not `native_decide`.
-/
namespace Erdos882Korsky.NegativeControls

private def a2 (i : Fin 2) : ℕ := if i = 0 then 1 else 2
private def a3 (i : Fin 3) : ℕ := if i = 0 then 4 else if i = 1 then 6 else 7
private def u (i : Fin 3) : Fin 3 := if i = 0 then 2 else if i = 1 then 1 else 0
private def v (i : Fin 3) : Fin 3 := if i = 2 then 2 else 0

/-- Dropping NoDouble makes the sum bound false even for distinct positive entries. -/
example : (∀ i, 0 < a2 i) ∧ ¬ (2 * 2 ^ (2 - 1) ≤ total a2) := by
  decide

/-- This weight vector satisfies the exact ratio-two exclusion. -/
example : NoDouble a3 := by
  unfold NoDouble
  decide

/-- Dropping Ordered destroys injectivity even with NoDouble. -/
example : value a3 u = value a3 v ∧ u ≠ v ∧ ¬ Ordered u := by
  unfold Ordered
  decide

end Erdos882Korsky.NegativeControls
