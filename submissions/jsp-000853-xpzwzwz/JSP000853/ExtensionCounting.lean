import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Counting finite function extensions

The sampling argument for the lower bound uses uniformly chosen colourings.
This file isolates the basic count: fixing values on `k` coordinates leaves
`|β| ^ (|α| - k)` functions.
-/

namespace JSP000853

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A function with prescribed values on `T` is equivalent to an arbitrary
function on the complement of `T`. -/
noncomputable def extensionEquiv (T : Finset α) (g : α → β) :
    {c : α → β // ∀ x ∈ T, c x = g x} ≃ ({x : α // x ∉ T} → β) := by
  classical
  refine
    { toFun := fun c x ↦ c.1 x
      invFun := fun h ↦
        ⟨fun x ↦ if hx : x ∈ T then g x else h ⟨x, hx⟩, by
          intro x hx
          simp [hx]⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ T
    · simp [hx, c.prop x hx]
    · simp [hx]
  · intro h
    funext x
    simp [x.prop]

theorem card_subtype_not_mem (T : Finset α) :
    Fintype.card {x : α // x ∉ T} = Fintype.card α - T.card := by
  classical
  rw [Fintype.card_subtype_compl]
  congr 1
  exact Fintype.card_coe T

theorem card_function_extensions (T : Finset α) (g : α → β) :
    Fintype.card {c : α → β // ∀ x ∈ T, c x = g x} =
      Fintype.card β ^ (Fintype.card α - T.card) := by
  classical
  calc
    Fintype.card {c : α → β // ∀ x ∈ T, c x = g x} =
        Fintype.card ({x : α // x ∉ T} → β) :=
      Fintype.card_congr (extensionEquiv T g)
    _ = Fintype.card β ^ Fintype.card {x : α // x ∉ T} := Fintype.card_fun
    _ = Fintype.card β ^ (Fintype.card α - T.card) := by
      rw [card_subtype_not_mem]

theorem card_filter_function_extensions (T : Finset α) (g : α → β) :
    ((Finset.univ : Finset (α → β)).filter fun c ↦ ∀ x ∈ T, c x = g x).card =
      Fintype.card β ^ (Fintype.card α - T.card) := by
  classical
  rw [← card_function_extensions T g]
  exact (Fintype.card_subtype _).symm

end JSP000853
