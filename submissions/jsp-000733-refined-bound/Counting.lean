import Moment
import Energy

open scoped BigOperators

namespace Erdos882Trial

/-- A twice-centered subset sum, over integers so subtraction is not truncated. -/
def centeredSum (A S : Finset ℕ) : ℤ :=
  2 * (∑ a ∈ S, (a : ℤ)) - ∑ a ∈ A, (a : ℤ)

/-- A nonoptimal second-moment bound which retains the sharp half-log-log coefficient. -/
theorem distinct_subset_sums_squared_bound {A : Finset ℕ} {n : ℕ}
    (hk : 2 ≤ A.card) (hbound : ∀ a ∈ A, a ≤ n)
    (hinj : Set.InjOn (fun S : Finset ℕ ↦ ∑ a ∈ S, a)
      (↑A.powerset : Set (Finset ℕ))) :
    4 ^ A.card ≤ 32 * A.card * n ^ 2 := by
  let t : ℕ := 2 ^ (A.card - 2)
  have hp : 2 ^ A.card = 4 * t := by
    calc
      2 ^ A.card = 2 ^ (2 + (A.card - 2)) := by congr 1; omega
      _ = 4 * t := by rw [pow_add]; rfl
  have ht : (0 : ℤ) < t := by
    exact_mod_cast (show 0 < t from pow_pos (by decide) _)
  have hpc : (2 : ℤ) ^ A.card = 4 * (t : ℤ) := by exact_mod_cast hp
  have hcenter : Set.InjOn (centeredSum A) (↑A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    apply hinj hS hT
    have heq' : (∑ a ∈ S, (a : ℤ)) = ∑ a ∈ T, (a : ℤ) := by
      unfold centeredSum at heq
      omega
    change (∑ a ∈ S, a) = ∑ a ∈ T, a
    apply Int.natCast_inj.mp
    simpa only [Nat.cast_sum] using heq'
  let Z : Finset ℤ := A.powerset.image (centeredSum A)
  have hcard : Z.card = 2 ^ A.card := by
    rw [Finset.card_image_iff.mpr hcenter, Finset.card_powerset]
  have henergy := integer_energy_lower_bound Z t (by rw [hcard, hp])
  have hmoment : (∑ x ∈ Z, x ^ 2) =
      (2 : ℤ) ^ A.card * ∑ a ∈ A, (a : ℤ) ^ 2 := by
    rw [Finset.sum_image (fun S hS T hT hST ↦ hcenter hS hT hST)]
    exact powerset_centered_sum_sq A (fun a ↦ (a : ℤ))
  rw [hmoment, hpc] at henergy
  have hsmall : (t : ℤ) ^ 2 ≤ 2 * ∑ a ∈ A, (a : ℤ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℤ) < 2 * t by omega)).mp
    nlinarith only [henergy]
  have hsquares : (∑ a ∈ A, (a : ℤ) ^ 2) ≤ (A.card : ℤ) * (n : ℤ) ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, (n : ℤ) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hn : (a : ℤ) ≤ n := by exact_mod_cast hbound a ha
        have ha0 : (0 : ℤ) ≤ a := by omega
        nlinarith
      _ = _ := by simp
  have hfour : (4 : ℤ) ^ A.card = ((2 : ℤ) ^ A.card) ^ 2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hresult : (4 : ℤ) ^ A.card ≤ 32 * (A.card : ℤ) * (n : ℤ) ^ 2 := by
    rw [hfour, hpc]
    nlinarith only [hsmall, hsquares]
  exact_mod_cast hresult

end Erdos882Trial

#print axioms Erdos882Trial.distinct_subset_sums_squared_bound
