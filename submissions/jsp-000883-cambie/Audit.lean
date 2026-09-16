import Cambie

namespace Erdos1063

/-- Mechanical alignment with the pinned Formal Conjectures definition. -/
theorem definition_alignment (k : ℕ) :
    n k = sInf {m : ℕ | 2 * k ≤ m ∧
      ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
        ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k} := rfl

/-- An independently written, fully explicit target type. -/
theorem target_alignment : ∀ k : ℕ, 3 ≤ k →
    sInf {m : ℕ | 2 * k ≤ m ∧
      ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
        ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}
      ≤ k * ((Finset.Icc 1 (k - 1)).lcm (id : ℕ → ℕ) : ℕ) := by
  intro k hk
  exact erdos_1063.variants.cambie_upper_bound hk

#check @erdos_1063.variants.cambie_upper_bound
#check @cambie_witness
#check @target_alignment
#print n
#print axioms choose_pred_eq_prod
#print axioms cambie_witness
#print axioms erdos_1063.variants.cambie_upper_bound
#print axioms definition_alignment
#print axioms target_alignment

end Erdos1063
