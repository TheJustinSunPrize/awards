import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Erdos882Trial

/-- At least half of a sufficiently large integer set lies outside `[-t,t)`. -/
theorem integer_energy_lower_bound (S : Finset ℤ) (t : ℕ)
    (hcard : 4 * t ≤ S.card) :
    (2 * t : ℤ) * (t : ℤ) ^ 2 ≤ ∑ x ∈ S, x ^ 2 := by
  let B : Finset ℤ := Finset.Ico (-(t : ℤ)) (t : ℤ)
  let L : Finset ℤ := S \ B
  have hB : B.card = 2 * t := by
    simp only [B, Int.card_Ico]
    omega
  have hL : 2 * t ≤ L.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := S) (t := B)
    change S.card ≤ L.card + B.card at h
    omega
  have hsq : ∀ x ∈ L, (t : ℤ) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hout : ¬ (-(t : ℤ) ≤ x ∧ x < (t : ℤ)) := by
      simpa only [B, Finset.mem_Ico] using (Finset.mem_sdiff.mp hx).2
    have ht : (0 : ℤ) ≤ t := by omega
    by_cases hxt : (t : ℤ) ≤ x
    · have hprod := mul_nonneg (by omega : (0 : ℤ) ≤ x - t)
        (by omega : (0 : ℤ) ≤ x + t)
      nlinarith only [hprod]
    · have hneg : x < -(t : ℤ) := by omega
      have hprod := mul_nonneg (by omega : (0 : ℤ) ≤ -x - t)
        (by omega : (0 : ℤ) ≤ -x + t)
      nlinarith only [hprod]
  have hLcast : (2 * t : ℤ) ≤ (L.card : ℤ) := by exact_mod_cast hL
  calc
    (2 * t : ℤ) * (t : ℤ) ^ 2 ≤ (L.card : ℤ) * (t : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hLcast (sq_nonneg _)
    _ = ∑ _x ∈ L, (t : ℤ) ^ 2 := by simp
    _ ≤ ∑ x ∈ L, x ^ 2 := Finset.sum_le_sum hsq
    _ ≤ ∑ x ∈ S, x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro x _ _
      exact sq_nonneg x

end Erdos882Trial

#print axioms Erdos882Trial.integer_energy_lower_bound
