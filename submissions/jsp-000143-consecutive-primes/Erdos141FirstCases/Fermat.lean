import Mathlib.FieldTheory.Finite.Basic

namespace Erdos141FirstCases

/-- A failed Fermat congruence is a compositeness certificate. -/
theorem not_prime_of_fermat (p a : ℕ) (h : (a : ZMod p) ^ p ≠ (a : ZMod p)) :
    ¬p.Prime := by
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  exact h (ZMod.pow_card _)

end Erdos141FirstCases
