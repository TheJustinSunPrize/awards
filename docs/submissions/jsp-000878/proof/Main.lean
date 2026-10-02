/-
JSP-000878: statement bridge and consequences of Luca's classification.
The imported complete formalization is attributed and pinned in source-lock.json.
This file does not claim a new mathematical result or first formalization.
-/
import ErdosProblems.Erdos1058
import JSP000878.Statement

namespace JSP000878

/-- Full classification, using the source's explicitly documented prime indexing.
`lowerEndpoint 0 = 1` handles the first prime interval without a fictitious prime. -/
theorem classification (n : ℕ) :
    SupportedFactorial n ↔
    1 ≤ n ∧ n ≤ 5 := by
  change Erdos1058.IsSolution n ↔ 1 ≤ n ∧ n ≤ 5
  rw [Erdos1058.erdos_1058]
  omega

/-- The original finiteness question, with all positive integers quantified. -/
theorem finitely_many_solutions :
    OriginalQuestion := by
  change Set.Finite {n : ℕ | SupportedFactorial n}
  have heq : {n : ℕ | SupportedFactorial n} = Set.Icc 1 5 := by
    ext n
    exact classification n
  rw [heq]
  exact Set.finite_Icc 1 5

/-- No finite search cutoff is assumed: for every n >= 6 and its prime interval,
there is a prime divisor of n!+1 outside the two permitted primes. -/
theorem escaping_prime (n k : ℕ) (hn : 6 ≤ n)
    (hlo : Erdos1058.lowerEndpoint k ≤ n)
    (hhi : n < Erdos1058.primeAt k) :
    ∃ r : ℕ, Nat.Prime r ∧ r ∣ Nat.factorial n + 1 ∧
      r ≠ Erdos1058.primeAt k ∧ r ≠ Erdos1058.primeAt (k + 1) := by
  classical
  by_contra h
  push_neg at h
  have hs : Erdos1058.IsSolution n := by
    refine ⟨by omega, k, hlo, hhi, ?_⟩
    intro r hr hd
    by_cases heq : r = Erdos1058.primeAt k
    · exact Or.inl heq
    · exact Or.inr (h r hr hd heq)
  have := (classification n).mp hs
  omega

#print axioms classification
#print axioms finitely_many_solutions
#print axioms escaping_prime
end JSP000878
