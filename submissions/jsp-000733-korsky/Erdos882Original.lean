import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log

/-!
# The finite extremal quantity in Erdős Problem 882

These definitions encode the original mathematical question: how many distinct
positive integers at most `n` can have primitive nonempty subset sums? The
maximum is defined as the maximum element of the finite set of attainable
cardinalities. No published lower-bound construction is incorporated here.
-/

open scoped BigOperators

namespace Erdos882

/-- Values of sums of nonempty subsets, with repeated values identified. -/
def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun U => ∑ a ∈ U, a

/-- Divisibility within a primitive set forces the two values to agree. -/
def IsPrimitive (B : Finset ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ∣ y → x = y

/-- The precise admissibility condition for the original finite problem. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsPrimitive (nonemptySubsetSums A)

lemma subsetSum_mem {A U : Finset ℕ} (hU : U ⊆ A) (hne : U.Nonempty) :
    (∑ a ∈ U, a) ∈ nonemptySubsetSums A := by
  apply Finset.mem_image.mpr
  refine ⟨U, Finset.mem_erase.mpr ?_, rfl⟩
  exact ⟨hne.ne_empty, Finset.mem_powerset.mpr hU⟩

/-- All cardinalities attained by admissible subsets of the interval. -/
noncomputable def attainableSizes (n : ℕ) : Finset ℕ := by
  classical
  exact (((Finset.Icc 1 n).powerset).filter
    (fun A => IsPrimitive (nonemptySubsetSums A))).image Finset.card

lemma mem_attainableSizes {n k : ℕ} :
    k ∈ attainableSizes n ↔ ∃ A : Finset ℕ, Admissible n A ∧ A.card = k := by
  classical
  simp only [attainableSizes, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset, Admissible]

lemma attainableSizes_nonempty (n : ℕ) : (attainableSizes n).Nonempty := by
  refine ⟨0, mem_attainableSizes.mpr ⟨∅, ?_, rfl⟩⟩
  simp [Admissible, IsPrimitive, nonemptySubsetSums]

/-- The maximum is an actual maximum of the finite collection of possible sizes. -/
noncomputable def maximumSize (n : ℕ) : ℕ :=
  (attainableSizes n).max' (attainableSizes_nonempty n)

lemma maximumSize_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = maximumSize n := by
  apply mem_attainableSizes.mp
  exact Finset.max'_mem _ _

lemma card_le_maximumSize {n : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    A.card ≤ maximumSize n := by
  have hmem := mem_attainableSizes.mpr ⟨A, hA, rfl⟩
  exact Finset.le_max' (attainableSizes n) A.card hmem

end Erdos882
