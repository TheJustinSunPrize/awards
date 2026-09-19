import KorskyDefs
import Erdos882Original

/-!
Bridge from primitive subset-sum sets to Korsky's packing theorem. This module
uses the independently defined finite extremal function in Erdos882Original.
Its packing hypothesis is discharged by the final Erdos882Korsky module.
-/

open scoped BigOperators

namespace Erdos882Korsky

noncomputable def enumerate (A : Finset ℕ) : Fin A.card ↪ ℕ where
  toFun i := (A.equivFin.symm i).val
  inj' := by
    intro i j hij
    exact A.equivFin.symm.injective (Subtype.ext hij)

lemma enumerate_mem (A : Finset ℕ) (i : Fin A.card) : enumerate A i ∈ A :=
  (A.equivFin.symm i).property

lemma indexed_subsum_mem (A : Finset ℕ) (I : Finset (Fin A.card)) (hI : I.Nonempty) :
    (∑ i ∈ I, enumerate A i) ∈ Erdos882.nonemptySubsetSums A := by
  classical
  have hsub : I.map (enumerate A) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact enumerate_mem A i
  have hmem := Erdos882.subsetSum_mem hsub hI.map
  simpa using hmem

lemma admissible_noDouble {n : ℕ} {A : Finset ℕ} (hA : Erdos882.Admissible n A) :
    NoDouble (enumerate A) := by
  classical
  intro I J hI hJ hdouble
  have hpos : 0 < ∑ j ∈ J, enumerate A j := by
    apply Finset.sum_pos
    · intro j hj
      exact (Finset.mem_Icc.mp (hA.1 (enumerate_mem A j))).1
    · exact hJ
  have hdiv : (∑ j ∈ J, enumerate A j) ∣ ∑ i ∈ I, enumerate A i := by
    rw [hdouble]
    exact dvd_mul_left _ _
  have heq := hA.2 _ (indexed_subsum_mem A J hJ) _
    (indexed_subsum_mem A I hI) hdiv
  omega

lemma admissible_total_le {n : ℕ} {A : Finset ℕ} (hA : Erdos882.Admissible n A) :
    total (enumerate A) ≤ A.card * n := by
  calc
    total (enumerate A) ≤ ∑ _ : Fin A.card, n := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_Icc.mp (hA.1 (enumerate_mem A i))).2
    _ = A.card * n := by simp

/-- The concrete original finite-set bound, conditional only on the supplied
proved packing lemma. -/
theorem admissible_card_le_log_add_one
    (hbound : ∀ {k : ℕ}, 0 < k → ∀ a : Fin k → ℕ,
      (∀ i, 0 < a i) → NoDouble a → k * 2 ^ (k - 1) ≤ total a)
    {n : ℕ} {A : Finset ℕ} (hA : Erdos882.Admissible n A) :
    A.card ≤ Nat.log 2 n + 1 := by
  by_cases hzero : A.card = 0
  · omega
  have hk : 0 < A.card := Nat.pos_of_ne_zero hzero
  have hp := hbound hk (enumerate A) (fun i ↦
    (Finset.mem_Icc.mp (hA.1 (enumerate_mem A i))).1) (admissible_noDouble hA)
  have hprod := hp.trans (admissible_total_le hA)
  have hpow : 2 ^ (A.card - 1) ≤ n := by
    nlinarith
  have hlog := Nat.le_log_of_pow_le (by omega : 1 < 2) hpow
  omega

/-- The upper bound concerns the attained maximum in the original problem. -/
theorem maximumSize_le_log_add_one
    (hbound : ∀ {k : ℕ}, 0 < k → ∀ a : Fin k → ℕ,
      (∀ i, 0 < a i) → NoDouble a → k * 2 ^ (k - 1) ≤ total a)
    (n : ℕ) : Erdos882.maximumSize n ≤ Nat.log 2 n + 1 := by
  obtain ⟨A, hA, hcard⟩ := Erdos882.maximumSize_attained n
  rw [← hcard]
  exact admissible_card_le_log_add_one hbound hA


end Erdos882Korsky
