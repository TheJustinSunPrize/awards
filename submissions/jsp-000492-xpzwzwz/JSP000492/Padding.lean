import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

namespace JSP000492

/-- A finite configuration in an infinite set can be padded to any larger size. -/
theorem pad_finite_set {α : Type*} {A : Set α} (hA : A.Infinite)
    (S : Finset α) (hS : ∀ x ∈ S, x ∈ A) (n : ℕ) (hn : S.card ≤ n) :
    ∃ T : Finset α, S ⊆ T ∧ T.card = n ∧ ∀ x ∈ T, x ∈ A := by
  classical
  obtain ⟨U, hU, hcard⟩ := (hA.sdiff S.finite_toSet).exists_subset_card_eq (n - S.card)
  have hdis : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro x hx hxU
    exact (hU hxU).2 hx
  refine ⟨S ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, hcard]
    omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hS x hx
    · exact (hU hx).1

end JSP000492
