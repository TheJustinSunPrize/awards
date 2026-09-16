import Mathlib

namespace JSP000179

open scoped BigOperators
set_option autoImplicit false

/-- The triangular-number term in Bosznay's construction. -/
def tri (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Bosznay's integer construction, indexed by `1 ≤ i < q`. -/
def bosznay (q : ℕ) (i : Fin (q - 1)) : ℕ :=
  let n := i.1 + 1
  n * q ^ 3 + tri n

/-- The exact finite non-averaging condition for the indexed construction.
The equation is the denominator-free form of saying that an element is the
average of a nonempty subset not containing it. -/
def IsNonAveraging (q : ℕ) : Prop :=
  ∀ i : Fin (q - 1), ∀ s : Finset (Fin (q - 1)),
    i ∉ s → s.Nonempty →
      (∑ j ∈ s, bosznay q j) ≠ s.card * bosznay q i

/-- The denominator-free definition of a non-averaging finite set of positive
integers. -/
def NonAveragingSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ t : Finset ℕ, t ⊆ A → a ∉ t → t.Nonempty →
    (∑ x ∈ t, x) ≠ t.card * a

/-- The set of values in the construction, with duplicate values removed by
`Finset.image` (the proof below establishes that there are no duplicates). -/
def BosznaySet (q : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (q - 1))).image (bosznay q)

end JSP000179
