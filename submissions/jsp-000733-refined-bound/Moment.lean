import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
The second-moment identity used in the Erdős 882 development.
This identity holds for all finite integer weights; alone it does not prove the upper bound.
-/

namespace Erdos882Trial

/-- The sum of squares of twice-centered subset sums. -/
theorem powerset_centered_sum_sq {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → ℤ) :
    (∑ S ∈ A.powerset, (2 * ∑ a ∈ S, f a - ∑ a ∈ A, f a) ^ 2) =
      (2 : ℤ) ^ A.card * ∑ a ∈ A, (f a) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha]
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      pow_succ (2 : ℤ) A.card]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ S ∈ A.powerset,
          ((2 : ℤ) * (2 * ∑ b ∈ S, f b - ∑ b ∈ A, f b) ^ 2 + 2 * (f a) ^ 2) := by
        apply Finset.sum_congr rfl
        intro S hS
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        rw [Finset.sum_insert haS]
        ring
      _ = (2 : ℤ) ^ A.card * 2 * ((f a) ^ 2 + ∑ b ∈ A, (f b) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const,
          nsmul_eq_mul, Finset.card_powerset]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        ring

#check @powerset_centered_sum_sq
#print axioms powerset_centered_sum_sq

end Erdos882Trial
