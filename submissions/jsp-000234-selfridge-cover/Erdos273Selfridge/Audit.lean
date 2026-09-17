import Erdos273Selfridge

namespace Erdos273SelfridgeAudit

-- Formal Conjectures' answer(True) is the proposition True.
theorem exact_public_statement : True ↔ ∃ c : StrictCoveringSystem ℕ,
    ∀ i, ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ c.moduli i = Ideal.span {p - 1} := by
  exact ⟨fun _ ↦ Erdos273Selfridge.variants_three, fun _ ↦ True.intro⟩

-- A separate arithmetic statement checks coverage of all integers, including negatives.
theorem integer_cover_exists : ∃ m r : Fin 12 → ℕ,
    Function.Injective m ∧ (∀ i, 2 ≤ m i ∧ (m i + 1).Prime) ∧
      ∀ n : ℤ, ∃ i, n % (m i : ℤ) = r i := by
  refine ⟨Erdos273Selfridge.modulus, Erdos273Selfridge.residue,
    Erdos273Selfridge.modulus_injective, ?_, Erdos273Selfridge.covers_int⟩
  intro i
  exact ⟨Erdos273Selfridge.modulus_two_le i, (Erdos273Selfridge.modulus_prime i).1⟩

-- This certificate relies on its modulus 2 (prime 3); it is not a p ≥ 5 solution.
example : Erdos273Selfridge.modulus 0 = 2 := rfl
example : ¬∃ i : Fin 12, i ≠ 0 ∧ 0 % Erdos273Selfridge.modulus i =
    Erdos273Selfridge.residue i := by decide

#print axioms Erdos273Selfridge.variants_three
#print axioms exact_public_statement
#print axioms integer_cover_exists
#check @exact_public_statement

end Erdos273SelfridgeAudit
