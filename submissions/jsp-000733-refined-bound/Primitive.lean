/-
Licensed under the Apache License, Version 2.0.

The proofs of `disjoint_equal_sums_impossible` and
`subset_sum_injective_of_primitive` are adapted from Erdos882Upper.lean:
https://github.com/zifanersuotang/awards/blob/83f20bbe58d116a9a290c86821fa4ee1a29dd3eb/submissions/jsp-000733/Erdos882Upper.lean
Source package: TheJustinSunPrize/awards PR #31, head
83f20bbe58d116a9a290c86821fa4ee1a29dd3eb.
Its NOTICE credits the added bridge and analytic assembly to Codex.
Its LICENSE explicitly applies Apache-2.0 to these added proof files.

Changes: independent quantified-subset definitions, a proved equivalence to
the primitive nonempty-subset-sum image formulation, and an application to the
new second-moment finite bound. No Erdos882Existing.lean source is imported or
copied. The original mathematical primitivity observation is recorded at
https://www.erdosproblems.com/882 .
-/
import Counting
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Erdos882Trial

/-- Distinct numerical nonempty subset sums do not divide one another; injectivity is not assumed. -/
def HasPrimitiveSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ∀ T ⊆ A, T.Nonempty →
    (∑ a ∈ S, a) ∣ (∑ a ∈ T, a) → (∑ a ∈ S, a) = ∑ a ∈ T, a

/-- The positive integer interval and primitive subset-sum condition of the original problem. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧ HasPrimitiveSubsetSums A

/-- Primitivity of the image of nonempty subset sums, as expressed mathematically in PR #31. -/
def PrimitiveImageCondition (A : Finset ℕ) : Prop :=
  let values := (A.powerset.filter (fun S ↦ S.Nonempty)).image (fun S ↦ ∑ a ∈ S, a)
  ∀ x ∈ values, ∀ y ∈ values, x ∣ y → x = y

/-- The quantified-subset definition is equivalent to primitivity of the numerical image. -/
theorem primitive_condition_iff_image (A : Finset ℕ) :
    HasPrimitiveSubsetSums A ↔ PrimitiveImageCondition A := by
  constructor
  · intro h x hx y hy hdiv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hy
    exact h S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
      (Finset.mem_filter.mp hS).2 T
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
      (Finset.mem_filter.mp hT).2 hdiv
  · intro h S hSA hS T hTA hT hdiv
    apply h _ ?_ _ ?_ hdiv
    · exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSA, hS⟩, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTA, hT⟩, rfl⟩

/-- Full equivalence of the interval and numerical-image conditions. -/
theorem admissible_iff_interval_image (n : ℕ) (A : Finset ℕ) :
    Admissible n A ↔ A ⊆ Finset.Icc 1 n ∧ PrimitiveImageCondition A := by
  constructor
  · rintro ⟨hbound, hprim⟩
    exact ⟨fun a ha ↦ Finset.mem_Icc.mpr (hbound a ha),
      (primitive_condition_iff_image A).mp hprim⟩
  · rintro ⟨hbound, hprim⟩
    exact ⟨fun a ha ↦ Finset.mem_Icc.mp (hbound ha),
      (primitive_condition_iff_image A).mpr hprim⟩

/-- Disjoint equal-sum subsets produce positive nonempty subset sums `s` and `2s`. -/
lemma disjoint_equal_sums_impossible {A S T : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hprimitive : HasPrimitiveSubsetSums A)
    (hSA : S ⊆ A) (hTA : T ⊆ A) (hST : Disjoint S T)
    (hS : S.Nonempty) (heq : (∑ a ∈ S, a) = ∑ a ∈ T, a) : False := by
  obtain ⟨a, ha⟩ := hS
  have hpositive : 0 < ∑ a ∈ S, a :=
    Finset.sum_pos_iff.mpr ⟨a, ha, hpos a (hSA ha)⟩
  have hsumUnion : (∑ a ∈ S ∪ T, a) = (∑ a ∈ S, a) * 2 := by
    rw [Finset.sum_union hST, ← heq, Nat.mul_two]
  have hdiv : (∑ a ∈ S, a) ∣ ∑ a ∈ S ∪ T, a := ⟨2, hsumUnion⟩
  have hbad := hprimitive S hSA ⟨a, ha⟩ (S ∪ T)
    (Finset.union_subset hSA hTA) ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩ hdiv
  omega

/-- Positivity and primitivity imply injectivity on all subsets, including the empty subset. -/
theorem subset_sum_injective_of_primitive {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hprimitive : HasPrimitiveSubsetSums A) :
    Set.InjOn (fun S : Finset ℕ ↦ ∑ a ∈ S, a)
      (↑A.powerset : Set (Finset ℕ)) := by
  intro S hS T hT heq
  have hSA : S ⊆ A := Finset.mem_powerset.mp hS
  have hTA : T ⊆ A := Finset.mem_powerset.mp hT
  have hdiff : (∑ a ∈ S \ T, a) = ∑ a ∈ T \ S, a :=
    Finset.sum_sdiff_eq_sum_sdiff_iff.mpr heq
  have hempty : S \ T = ∅ := by
    by_contra hne
    have hd : Disjoint (S \ T) (T \ S) := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxS).2 (Finset.mem_sdiff.mp hxT).1
    exact disjoint_equal_sums_impossible hpos hprimitive
      (Finset.sdiff_subset.trans hSA) (Finset.sdiff_subset.trans hTA)
      hd (Finset.nonempty_iff_ne_empty.mpr hne) hdiff
  have hempty' : T \ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hpositive : 0 < ∑ a ∈ T \ S, a :=
      Finset.sum_pos_iff.mpr
        ⟨x, hx, hpos x (hTA (Finset.mem_sdiff.mp hx).1)⟩
    rw [hempty, Finset.sum_empty] at hdiff
    omega
  exact Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp hempty)
    (Finset.sdiff_eq_empty_iff_subset.mp hempty')

/-- The squared exponential bound for admissible sets, with no extra injectivity hypothesis. -/
theorem admissible_squared_bound {n : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hk : 2 ≤ A.card) :
    4 ^ A.card ≤ 32 * A.card * n ^ 2 := by
  exact distinct_subset_sums_squared_bound hk (fun a ha ↦ (hA.1 a ha).2)
    (subset_sum_injective_of_primitive (fun a ha ↦ (hA.1 a ha).1) hA.2)

end Erdos882Trial

#check @Erdos882Trial.admissible_squared_bound
#print axioms Erdos882Trial.primitive_condition_iff_image
#print axioms Erdos882Trial.admissible_iff_interval_image
#print axioms Erdos882Trial.subset_sum_injective_of_primitive
#print axioms Erdos882Trial.admissible_squared_bound
