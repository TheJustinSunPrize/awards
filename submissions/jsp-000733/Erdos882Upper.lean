import Erdos882Existing

/-!
# The upper-bound bridge for Erdős Problem 882

The lower construction and the definitions are imported, unchanged, from
`plby/lean-proofs` at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
This file supplies the missing implication from primitive nonempty subset sums
to injectivity of the subset-sum map, then the elementary counting upper bound.

The observation that admissibility implies distinct subset sums is recorded on
the original Erdős problem page. Counting bounds under an already-assumed
distinct-subset-sums hypothesis were previously formalized in
`rjwalters/lean-genius`, `Erdos882ProblemOQ03.lean`, commit
`dc62f771ed5010abfdb04247dff6143e0e69d3e7`. The counting argument below is
reproved directly against the definitions used by the existing lower bound;
this package contributes the bridge and complete asymptotic assembly relative
to that checked prior work, without a claim of global formalization priority.
-/

open scoped BigOperators

namespace Erdos882

lemma sum_mem_nonemptySubsetSums_of_subset {A S : Finset ℕ}
    (hSA : S ⊆ A) (hS : S.Nonempty) :
    (∑ a ∈ S, a) ∈ nonemptySubsetSums A := by
  exact Finset.mem_image.mpr
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSA, hS⟩, rfl⟩

/-- Disjoint subsets of a positive admissible set cannot have the same
positive sum: their union would produce both `s` and `2s` in a primitive set. -/
lemma disjoint_equal_sums_impossible {A S T : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a)
    (hprimitive : IsPrimitive (nonemptySubsetSums A))
    (hSA : S ⊆ A) (hTA : T ⊆ A) (hST : Disjoint S T)
    (hS : S.Nonempty) (heq : (∑ a ∈ S, a) = ∑ a ∈ T, a) : False := by
  obtain ⟨a, ha⟩ := hS
  have hpositive : 0 < ∑ a ∈ S, a :=
    Finset.sum_pos_iff.mpr ⟨a, ha, hpos a (hSA ha)⟩
  have hmemS := sum_mem_nonemptySubsetSums_of_subset hSA ⟨a, ha⟩
  have hmemUnion := sum_mem_nonemptySubsetSums_of_subset
    (Finset.union_subset hSA hTA) ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩
  have hsumUnion : (∑ a ∈ S ∪ T, a) = (∑ a ∈ S, a) * 2 := by
    rw [Finset.sum_union hST, ← heq, Nat.mul_two]
  have hdiv : (∑ a ∈ S, a) ∣ ∑ a ∈ S ∪ T, a := ⟨2, hsumUnion⟩
  have hbad := hprimitive _ hmemS _ hmemUnion hdiv
  omega

/-- The sum map is injective on every subset, including the empty subset,
of a positive set with primitive nonempty subset sums. -/
theorem subset_sum_injective_of_primitive {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a)
    (hprimitive : IsPrimitive (nonemptySubsetSums A)) :
    Set.InjOn (fun S : Finset ℕ ↦ ∑ a ∈ S, a) (↑A.powerset : Set (Finset ℕ)) := by
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

/-- All `2^|A|` subsets have distinct sums in `[0,n|A|]`. -/
theorem pow_card_le_mul_add_one {n : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) : 2 ^ A.card ≤ n * A.card + 1 := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha ↦
    (Finset.mem_Icc.mp (hA.1 ha)).1
  have hinj := subset_sum_injective_of_primitive hpos hA.2
  have hcard : (A.powerset.image (fun S ↦ ∑ a ∈ S, a)).card = 2 ^ A.card := by
    rw [Finset.card_image_iff.mpr hinj, Finset.card_powerset]
  have hsub : A.powerset.image (fun S ↦ ∑ a ∈ S, a) ⊆
      Finset.range (n * A.card + 1) := by
    intro s hs
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
    have hSA : S ⊆ A := Finset.mem_powerset.mp hS
    have hsum : (∑ a ∈ S, a) ≤ n * A.card := by
      calc
        (∑ a ∈ S, a) ≤ ∑ _a ∈ S, n := Finset.sum_le_sum fun a ha ↦
          (Finset.mem_Icc.mp (hA.1 (hSA ha))).2
        _ = n * S.card := by simp [Nat.mul_comm]
        _ ≤ n * A.card := Nat.mul_le_mul_left n (Finset.card_le_card hSA)
    exact Finset.mem_range.mpr (by omega)
  have h := Finset.card_le_card hsub
  simpa only [hcard, Finset.card_range] using h

/-- The actual finite maximum in the problem satisfies the same upper bound. -/
theorem maximumSize_pow_le (n : ℕ) :
    2 ^ maximumSize n ≤ n * maximumSize n + 1 := by
  obtain ⟨A, hA, hcard⟩ := maximumSize_attained n
  simpa only [hcard] using pow_card_le_mul_add_one hA

end Erdos882

#print axioms Erdos882.subset_sum_injective_of_primitive
#print axioms Erdos882.maximumSize_pow_le
