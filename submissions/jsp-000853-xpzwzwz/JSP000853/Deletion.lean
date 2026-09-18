import JSP000853.Definitions
import Mathlib.Data.Finset.Prod

/-!
# Deterministic deletion of violations

This is the non-probabilistic half of the lower-bound argument.  Starting from
an arbitrary sampled set, remove every value produced by a bad internal pair.
The remaining set is free, and at most one vertex is charged to each bad pair.
-/

namespace JSP000853

namespace PairMapping

variable {α : Type*} [DecidableEq α]

/-- Ordered pairs inside `R` whose image also lies in `R`.  Counting ordered
pairs is deliberately convenient; it is only an upper bound on violations. -/
def badPairs (f : PairMapping α) (R : Finset α) : Finset (α × α) :=
  R.offDiag.filter fun p ↦ f p.1 p.2 ∈ R

/-- Values to delete in order to destroy every violation internal to `R`. -/
def badOutputs (f : PairMapping α) (R : Finset α) : Finset α :=
  (f.badPairs R).image fun p ↦ f p.1 p.2

/-- The free set obtained by deleting all bad outputs from `R`. -/
def cleaned (f : PairMapping α) (R : Finset α) : Finset α :=
  R \ f.badOutputs R

theorem cleaned_subset (f : PairMapping α) (R : Finset α) : f.cleaned R ⊆ R :=
  Finset.sdiff_subset

theorem cleaned_isFree (f : PairMapping α) (R : Finset α) : f.IsFree (f.cleaned R) := by
  intro x hx y hy hxy hmem
  have hxR : x ∈ R := (Finset.mem_sdiff.mp hx).1
  have hyR : y ∈ R := (Finset.mem_sdiff.mp hy).1
  have hmemR : f x y ∈ R := (Finset.mem_sdiff.mp hmem).1
  have hpair : (x, y) ∈ f.badPairs R := by
    simp [badPairs, Finset.mem_offDiag, hxR, hyR, hxy, hmemR]
  have hout : f x y ∈ f.badOutputs R := by
    exact Finset.mem_image.mpr ⟨(x, y), hpair, rfl⟩
  exact (Finset.mem_sdiff.mp hmem).2 hout

theorem card_le_cleaned_add_badPairs (f : PairMapping α) (R : Finset α) :
    R.card ≤ (f.cleaned R).card + (f.badPairs R).card := by
  have hcover : R ⊆ f.cleaned R ∪ f.badOutputs R := by
    intro x hx
    by_cases hout : x ∈ f.badOutputs R
    · exact Finset.mem_union_right _ hout
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hout⟩)
  calc
    R.card ≤ (f.cleaned R ∪ f.badOutputs R).card := Finset.card_le_card hcover
    _ ≤ (f.cleaned R).card + (f.badOutputs R).card :=
      Finset.card_union_le _ _
    _ ≤ (f.cleaned R).card + (f.badPairs R).card := by
      exact Nat.add_le_add_left Finset.card_image_le _

theorem le_card_cleaned_of_add_le_card (f : PairMapping α) {R : Finset α} {t : ℕ}
    (h : (f.badPairs R).card + t ≤ R.card) : t ≤ (f.cleaned R).card := by
  apply Nat.le_of_add_le_add_left
  calc
    (f.badPairs R).card + t ≤ R.card := h
    _ ≤ (f.cleaned R).card + (f.badPairs R).card := f.card_le_cleaned_add_badPairs R
    _ = (f.badPairs R).card + (f.cleaned R).card := Nat.add_comm _ _

end PairMapping

end JSP000853
