import Erdos261Finite.FiniteBound

set_option maxRecDepth 4096

-- Restated independently in the exact shape of the public conjecture.
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
      (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ) :=
  Erdos261Finite.le_10000 hn_pos hn

#print axioms Erdos261Finite.transfer
#print axioms Erdos261Finite.run_transfer
#print axioms Erdos261Finite.property_of_tail
#print axioms Erdos261Finite.le_10000
#print Erdos261Finite.le_10000
