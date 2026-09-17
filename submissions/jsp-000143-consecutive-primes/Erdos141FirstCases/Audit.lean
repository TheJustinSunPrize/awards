import Erdos141FirstCases

namespace Erdos141FirstCases.Audit

def ReferenceAP (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a d : ℕ, ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def ReferencePrimeProgression (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a, ENat.card s = l ∧ s = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}

example (s : Set ℕ) (l : ℕ∞) : ReferenceAP s l ↔ s.IsAPOfLength l := Iff.rfl
example (s : Set ℕ) (l : ℕ∞) :
    ReferencePrimeProgression s l ↔ Erdos141.Set.IsPrimeProgressionOfLength s l := Iff.rfl

/-- The original target with both definitions independently expanded. -/
theorem exact_statement : ∀ (k : ℕ), 3 ≤ k → k ≤ 10 →
    ∃ s : Set ℕ, ReferenceAP s k ∧ ReferencePrimeProgression s k :=
  Erdos141.erdos_141.variants.first_cases

/-- The closed interval contains exactly the ten listed primes. -/
theorem exact_interval (n : ℕ) (hlo : start ≤ n) (hhi : n ≤ start + 1890) :
    n.Prime ↔ ∃ i < 10, n = start + i * 210 := by
  constructor
  · intro hp
    have hmod : (n - start) % 210 = 0 := by
      by_contra h
      have hc := composite_between (n - start) (by omega) h
      rw [Nat.add_sub_of_le hlo] at hc
      exact hc hp
    refine ⟨(n - start) / 210, by omega, ?_⟩
    omega
  · rintro ⟨i, hi, rfl⟩
    exact prime_term i hi

#print axioms Erdos141FirstCases.pratt
#print axioms Erdos141FirstCases.prime_term
#print axioms Erdos141FirstCases.composite_between
#print axioms Erdos141FirstCases.progression_from_certificates
#print axioms Erdos141.erdos_141.variants.first_cases
#print axioms exact_statement
#print axioms exact_interval

end Erdos141FirstCases.Audit
