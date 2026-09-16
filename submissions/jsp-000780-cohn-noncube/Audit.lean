import CohnNoncube

#print Nat.Full
#print Erdos939.Noncube
#check @Erdos939.noncube_triples_infinite
#print axioms Erdos939.cube_of_mul_cube
#print axioms Erdos939.noncube_mul_cube
#print axioms Erdos939.cohn_seed
#print axioms Erdos939.larger_noncube
#print axioms Erdos939.noncube_triples_infinite

/-- The target with the noncube predicate expanded, without seed or recurrence assumptions. -/
theorem cohn_noncube_statement :
    {t : ℕ × ℕ × ℕ |
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      t.1.Coprime t.2.1 ∧ t.1.Coprime t.2.2 ∧ t.2.1.Coprime t.2.2 ∧
      (∀ p ∈ t.1.primeFactors, p ^ 3 ∣ t.1) ∧
      (∀ p ∈ t.2.1.primeFactors, p ^ 3 ∣ t.2.1) ∧
      (∀ p ∈ t.2.2.primeFactors, p ^ 3 ∣ t.2.2) ∧
      t.1 + t.2.1 = t.2.2 ∧
      (¬ ∃ r : ℕ, r ^ 3 = t.1) ∧ (¬ ∃ r : ℕ, r ^ 3 = t.2.1) ∧
      (¬ ∃ r : ℕ, r ^ 3 = t.2.2)}.Infinite :=
  Erdos939.noncube_triples_infinite

#print axioms cohn_noncube_statement
