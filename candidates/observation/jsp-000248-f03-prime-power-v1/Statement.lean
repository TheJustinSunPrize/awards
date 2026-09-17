import Mathlib

open BigOperators

namespace JSP000248

/-- A finite Egyptian-fraction representation of `1` by distinct positive denominators.
A `Finset` supplies distinctness, and the first conjunct supplies positivity. -/
def IsEgyptianRep (s : Finset ℕ) : Prop :=
  (∀ n ∈ s, 0 < n) ∧ (∑ n ∈ s, (1 : ℚ) / n) = 1

/-- The source's prime-power obstruction, stated for a positive exponent. -/
def PrimePowerNotLargest (p a : ℕ) : Prop :=
  ¬ ∃ s : Finset ℕ,
      IsEgyptianRep s ∧ p ^ a ∈ s ∧ ∀ d ∈ s, d ≤ p ^ a

end JSP000248
