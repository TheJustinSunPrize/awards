import KorskyEndpoint
import Mathlib.Data.Finset.Sort

/-! Sorted enumeration and the original extremal-function interface for the
finite strengthening of Korsky's upper bound. The finite bound parameter in
this bridge is discharged by the final theorem module. -/
namespace Erdos882Korsky

noncomputable def orderedEnumerate (A : Finset ℕ) : Fin A.card ↪o ℕ :=
  A.orderEmbOfFin rfl

lemma orderedEnumerate_mem (A : Finset ℕ) (i : Fin A.card) :
    orderedEnumerate A i ∈ A := A.orderEmbOfFin_mem rfl i

lemma ordered_indexed_subsum_mem (A : Finset ℕ) (I : Finset (Fin A.card))
    (hI : I.Nonempty) :
    (∑ i ∈ I, orderedEnumerate A i) ∈ Erdos882.nonemptySubsetSums A := by
  classical
  have hsub : I.map (orderedEnumerate A).toEmbedding ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact orderedEnumerate_mem A i
  have hmem := Erdos882.subsetSum_mem hsub hI.map
  simpa using hmem

lemma admissible_ordered_noDouble {n : ℕ} {A : Finset ℕ}
    (hA : Erdos882.Admissible n A) : NoDouble (orderedEnumerate A) := by
  classical
  intro I J hI hJ hdouble
  have hpos : 0 < ∑ j ∈ J, orderedEnumerate A j := by
    apply Finset.sum_pos
    · intro j hj
      exact (Finset.mem_Icc.mp (hA.1 (orderedEnumerate_mem A j))).1
    · exact hJ
  have hdiv : (∑ j ∈ J, orderedEnumerate A j) ∣ ∑ i ∈ I, orderedEnumerate A i := by
    rw [hdouble]
    exact dvd_mul_left _ _
  have heq := hA.2 _ (ordered_indexed_subsum_mem A J hJ) _
    (ordered_indexed_subsum_mem A I hI) hdiv
  omega

lemma nonemptySubsetSums_mono {A B : Finset ℕ} (hBA : B ⊆ A) :
    Erdos882.nonemptySubsetSums B ⊆ Erdos882.nonemptySubsetSums A := by
  classical
  intro x hx
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hU
  exact Erdos882.subsetSum_mem
    ((Finset.mem_powerset.mp hsub).trans hBA) (Finset.nonempty_iff_ne_empty.mpr hne)

lemma admissible_subset {n : ℕ} {A B : Finset ℕ} (hA : Erdos882.Admissible n A)
    (hBA : B ⊆ A) : Erdos882.Admissible n B := by
  refine ⟨hBA.trans hA.1, ?_⟩
  intro x hx y hy hdiv
  exact hA.2 x (nonemptySubsetSums_mono hBA hx) y (nonemptySubsetSums_mono hBA hy) hdiv

theorem admissible_finite_bound_of_bound
    (hbound : ∀ {k n : ℕ}, 0 < k → ∀ a : Fin k → ℕ,
      (∀ i, 0 < a i) → StrictMono a → NoDouble a → (∀ i, a i ≤ n) →
      (k+1)*2^(k-1) + (k-1)^2/4 ≤ k*n+1)
    {n : ℕ} {A : Finset ℕ} (hA : Erdos882.Admissible n A) (hk : 0 < A.card) :
    (A.card+1)*2^(A.card-1) + (A.card-1)^2/4 ≤ A.card*n+1 := by
  apply hbound hk (orderedEnumerate A)
  · intro i
    exact (Finset.mem_Icc.mp (hA.1 (orderedEnumerate_mem A i))).1
  · exact (orderedEnumerate A).strictMono
  · exact admissible_ordered_noDouble hA
  · intro i
    exact (Finset.mem_Icc.mp (hA.1 (orderedEnumerate_mem A i))).2

/-- The strict threshold excludes an admissible subset of size m+1. The proof
uses subset closure, not an unproved monotonicity property of the threshold. -/
theorem maximumSize_le_of_finite_threshold
    (hbound : ∀ {k n : ℕ}, 0 < k → ∀ a : Fin k → ℕ,
      (∀ i, 0 < a i) → StrictMono a → NoDouble a → (∀ i, a i ≤ n) →
      (k+1)*2^(k-1) + (k-1)^2/4 ≤ k*n+1)
    (n m : ℕ) (hthreshold : (m+1)*n+1 < (m+2)*2^m + m^2/4) :
    Erdos882.maximumSize n ≤ m := by
  classical
  obtain ⟨A, hA, hcard⟩ := Erdos882.maximumSize_attained n
  by_contra h
  have hle : m+1 ≤ A.card := by omega
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq hle
  have hB := admissible_subset hA hBA
  have hb := admissible_finite_bound_of_bound hbound hB (by omega : 0 < B.card)
  rw [hBcard] at hb
  simp only [Nat.add_sub_cancel] at hb
  exact (not_le_of_gt hthreshold) (by simpa only [Nat.add_assoc] using hb)

end Erdos882Korsky
