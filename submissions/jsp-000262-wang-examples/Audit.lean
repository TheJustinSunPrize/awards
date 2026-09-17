module
public import WangExamples

public section

/-- Expanded statements use Mathlib's prime factors and squarefreeness directly. -/
theorem audited_nine :
    2 ≤ (5998279018951962402 : ℕ) ∧
    Squarefree (5998279018951962402 : ℕ) ∧
    (5998279018951962402 : ℕ).primeFactors.card = 9 ∧
    (∀ p ∈ (5998279018951962402 : ℕ).primeFactors, Nat.Prime p) ∧
    (∑ p ∈ (5998279018951962402 : ℕ).primeFactors, (1 : ℚ) / p) =
      1 - (1 : ℚ) / 5998279018951962402 := by
  exact ⟨JSP262.nine_primary_pseudoperfect.1,
    JSP262.nine_primary_pseudoperfect.2.1,
    JSP262.nine_prime_factors,
    fun _ hp ↦ (Nat.mem_primeFactors.mp hp).1,
    JSP262.original_equation JSP262.nine_primary_pseudoperfect⟩

theorem audited_ten :
    2 ≤ (35979351189199316534587473905773572006 : ℕ) ∧
    Squarefree (35979351189199316534587473905773572006 : ℕ) ∧
    (35979351189199316534587473905773572006 : ℕ).primeFactors.card = 10 ∧
    (∀ p ∈ (35979351189199316534587473905773572006 : ℕ).primeFactors, Nat.Prime p) ∧
    (∑ p ∈ (35979351189199316534587473905773572006 : ℕ).primeFactors, (1 : ℚ) / p) =
      1 - (1 : ℚ) / 35979351189199316534587473905773572006 := by
  exact ⟨JSP262.ten_primary_pseudoperfect.1,
    JSP262.ten_primary_pseudoperfect.2.1,
    JSP262.ten_prime_factors,
    fun _ hp ↦ (Nat.mem_primeFactors.mp hp).1,
    JSP262.original_equation JSP262.ten_primary_pseudoperfect⟩

#print axioms JSP262.prime_P10
#print axioms audited_nine
#print axioms audited_ten
