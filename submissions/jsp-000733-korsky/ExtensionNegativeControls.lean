import KorskyBalancedDefs
import KorskyBalancedLower

/-!
Small kernel-checked counterexamples guarding the hypotheses and endpoints of
Korsky's balanced-word estimates. These are proofs of explicit negations, not
additional prize claims. All finite computations use `decide`, whose generated
proof terms are checked by the Lean kernel.
-/
namespace Erdos882Korsky.ExtensionNegativeControls

private def increasingWeights (i : Fin 2) : ℕ := if i = 0 then 1 else 2
private def decreasingWeights (i : Fin 2) : ℕ := if i = 0 then 2 else 1
private def reversedWord (i : Fin 2) : Fin 3 := if i = 0 then 2 else 0
private def orderedWord (i : Fin 2) : Fin 3 := if i = 0 then 0 else 2
private def unitWeights (_ : Fin 3) : ℕ := 1
private def unitWord (_ : Fin 3) : Fin 3 := 1

/-- The coefficient sum alone cannot replace Ordered in the lower estimate. -/
theorem ordered_hypothesis_essential :
    Monotone increasingWeights ∧
    (∑ i, (reversedWord i).val) = 2 ∧
    ¬ Ordered reversedWord ∧
    value increasingWeights reversedWord < (total increasingWeights : ℤ) := by
  unfold Monotone Ordered value total increasingWeights reversedWord
  decide

/-- Balanced ordered words need monotone weights for the lower estimate. -/
theorem monotone_hypothesis_essential :
    Balanced orderedWord ∧
    ¬ Monotone decreasingWeights ∧
    value decreasingWeights orderedWord < (total decreasingWeights : ℤ) := by
  unfold Balanced Ordered Monotone value total decreasingWeights orderedWord
  decide

/-- Replacing strict monotonicity by monotonicity makes the upper estimate
false, even when all weights are positive and bounded by n=1. -/
theorem strictMono_hypothesis_essential :
    Monotone unitWeights ∧
    (∀ i, 0 < unitWeights i) ∧
    (∀ i, unitWeights i ≤ 1) ∧
    Balanced unitWord ∧
    ¬ StrictMono unitWeights ∧
    ¬ (value unitWeights unitWord + (((3 - 1)^2 / 4 : ℕ) : ℤ) ≤
      ((3 * 1 : ℕ) : ℤ)) := by
  unfold Monotone Balanced Ordered StrictMono value unitWeights unitWord
  decide

/-- The floor term is 0, 0, 1 for the first three positive sizes. -/
theorem first_floor_values :
    ((1 - 1)^2 / 4 : ℕ) = 0 ∧
    ((2 - 1)^2 / 4 : ℕ) = 0 ∧
    ((3 - 1)^2 / 4 : ℕ) = 1 := by
  decide

/-- For a single generator a=1, the closed interval consists of one value.
Deleting the final +1 in the deficit estimate would incorrectly assert 2≤1. -/
theorem interval_endpoint_one_essential :
    ((1 + 1) * 2^(1 - 1) + (1 - 1)^2 / 4 : ℕ) = 1 * 1 + 1 ∧
    ¬ ((1 + 1) * 2^(1 - 1) + (1 - 1)^2 / 4 ≤ (1 * 1 : ℕ)) := by
  decide

end Erdos882Korsky.ExtensionNegativeControls
