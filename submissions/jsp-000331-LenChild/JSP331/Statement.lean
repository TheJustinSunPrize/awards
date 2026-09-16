import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order

/-!
The sufficiently-large-cardinality inequality in JSP-000331.
This statement is separate from the stronger all-cardinalities conjecture.
-/

namespace JSP331

/-- The catalog statement, with division and comparison in the rationals. -/
def EventualGrahamStatement : Prop :=
  ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → 0 ∉ A → A.Nonempty →
    ∃ a ∈ A, ∃ b ∈ A, (a.gcd b : ℚ) ≤ (a : ℚ) / A.card

end JSP331
