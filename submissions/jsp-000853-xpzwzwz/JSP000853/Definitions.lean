import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Pair mappings and free sets

This file encodes the statement of Erdős Problem #1025 without committing the proof
to a particular representation of unordered pairs.
-/

namespace JSP000853

/-- An admissible map from unordered pairs of distinct elements of `α` back to `α`.

The binary function is required to be symmetric.  On distinct inputs its value is
different from both inputs, exactly as in Erdős Problem #1025.
-/
structure PairMapping (α : Type*) where
  toFun : α → α → α
  map_symm : ∀ x y, toFun x y = toFun y x
  map_ne_left : ∀ {x y}, x ≠ y → toFun x y ≠ x
  map_ne_right : ∀ {x y}, x ≠ y → toFun x y ≠ y

instance : CoeFun (PairMapping α) (fun _ => α → α → α) :=
  ⟨PairMapping.toFun⟩

/-- `S` is free (called independent in the source problem) when the image of every
pair of distinct members lies outside `S`. -/
def PairMapping.IsFree [DecidableEq α] (f : PairMapping α) (S : Finset α) : Prop :=
  ∀ {x}, x ∈ S → ∀ {y}, y ∈ S → x ≠ y → f x y ∉ S

namespace PairMapping

variable [DecidableEq α] (f : PairMapping α)

@[simp]
theorem isFree_empty : f.IsFree ∅ := by
  simp [IsFree]

@[simp]
theorem isFree_singleton (x : α) : f.IsFree {x} := by
  simp [IsFree]

theorem IsFree.mono {S T : Finset α} (hS : f.IsFree S) (hTS : T ⊆ S) : f.IsFree T := by
  intro x hx y hy hxy hmem
  exact hS (hTS hx) (hTS hy) hxy (hTS hmem)

theorem not_isFree_iff {S : Finset α} :
    ¬f.IsFree S ↔ ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x y ∈ S := by
  classical
  constructor
  · intro h
    simp only [IsFree, not_forall, Classical.not_not] at h
    obtain ⟨x, hx, y, hy, hxy, hmem⟩ := h
    exact ⟨x, hx, y, hy, hxy, hmem⟩
  · rintro ⟨x, hx, y, hy, hxy, hmem⟩ hfree
    exact hfree hx hy hxy hmem

end PairMapping

/-- A direct, square-root-free formulation of the universal lower-bound half of
`g(n) = Θ(√n)`.  A witness `C` says every admissible pair mapping has a free set
whose squared cardinality is at least `n / C`. -/
def LowerBoundTarget : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) (f : PairMapping (Fin n)),
    ∃ S : Finset (Fin n), f.IsFree S ∧ n ≤ C * S.card ^ 2

/-- A direct, square-root-free formulation of the construction half of
`g(n) = Θ(√n)`.  The small cases are excluded because no admissible mapping exists
on a type with fewer than three elements. -/
def UpperBoundTarget : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
    ∃ f : PairMapping (Fin n), ∀ S : Finset (Fin n), f.IsFree S → S.card ^ 2 ≤ C * n

/-- The complete formal target corresponding to the published asymptotic answer. -/
def Erdos1025Target : Prop := LowerBoundTarget ∧ UpperBoundTarget

end JSP000853
