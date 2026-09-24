import Primitive
import Mathlib.Data.Finset.Lattice.Fold

open scoped BigOperators

namespace Erdos882Trial

/-- All finite sets admissible in the original problem; this family includes the empty set. -/
noncomputable def admissibleFamily (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 n).powerset.filter (Admissible n)

/-- The actual maximum cardinality under the original primitive subset-sum condition. -/
noncomputable def maximumSize (n : ℕ) : ℕ :=
  (admissibleFamily n).sup Finset.card

theorem mem_admissibleFamily_iff {n : ℕ} {A : Finset ℕ} :
    A ∈ admissibleFamily n ↔ Admissible n A := by
  classical
  simp only [admissibleFamily, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact And.right
  · intro h
    exact ⟨((admissible_iff_interval_image n A).mp h).1, h⟩

theorem empty_admissible (n : ℕ) : Admissible n ∅ := by
  constructor
  · simp
  · intro S hS hne
    have : S = ∅ := Finset.subset_empty.mp hS
    simp [this] at hne

theorem admissibleFamily_nonempty (n : ℕ) : (admissibleFamily n).Nonempty :=
  ⟨∅, mem_admissibleFamily_iff.mpr (empty_admissible n)⟩

theorem cardinality_le_maximumSize {n : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) : A.card ≤ maximumSize n := by
  exact Finset.le_sup (f := Finset.card) (mem_admissibleFamily_iff.mpr hA)

theorem maximumSize_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = maximumSize n := by
  obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup
    (admissibleFamily n) (admissibleFamily_nonempty n) Finset.card
  exact ⟨A, mem_admissibleFamily_iff.mp hA, heq.symm⟩

theorem admissible_card_le {n : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    A.card ≤ n := by
  have hsub := ((admissible_iff_interval_image n A).mp hA).1
  have hcard := Finset.card_le_card hsub
  simpa using hcard

theorem maximumSize_le (n : ℕ) : maximumSize n ≤ n := by
  obtain ⟨A, hA, heq⟩ := maximumSize_attained n
  rw [← heq]
  exact admissible_card_le hA

/-- The order characterization of the actual maximum cardinality. -/
theorem maximumSize_characterization (n m : ℕ) :
    maximumSize n ≤ m ↔ ∀ A : Finset ℕ, Admissible n A → A.card ≤ m := by
  constructor
  · intro h A hA
    exact (cardinality_le_maximumSize hA).trans h
  · intro h
    obtain ⟨A, hA, heq⟩ := maximumSize_attained n
    rw [← heq]
    exact h A hA

/-- The maximum expanded using subsets of the interval and the numerical subset-sum image. -/
theorem maximumSize_definition_alignment (n : ℕ) :
    maximumSize n =
      (((Finset.Icc 1 n).powerset.filter fun A ↦
        ∀ x ∈ (A.powerset.filter (fun S ↦ S.Nonempty)).image (fun S ↦ ∑ a ∈ S, a),
        ∀ y ∈ (A.powerset.filter (fun S ↦ S.Nonempty)).image (fun S ↦ ∑ a ∈ S, a),
          x ∣ y → x = y).sup Finset.card) := by
  classical
  unfold maximumSize admissibleFamily
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hA⟩
    exact ⟨hsub, ((admissible_iff_interval_image n A).mp hA).2⟩
  · rintro ⟨hsub, hprim⟩
    exact ⟨hsub, (admissible_iff_interval_image n A).mpr ⟨hsub, hprim⟩⟩

end Erdos882Trial

#print axioms Erdos882Trial.maximumSize_attained
#print axioms Erdos882Trial.maximumSize_le
