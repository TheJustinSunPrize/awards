/- JSP-000878 original predicate, using only Mathlib definitions. -/
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

namespace JSP000878

/-- Every prime divisor of n!+1 lies among the first two primes after positive n.
The first prime interval starts at 1; 1 itself is not declared prime. -/
def SupportedFactorial (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ,
    (match k with
      | 0 => 1
      | i + 1 => Nat.nth Nat.Prime i) ≤ n ∧
    n < Nat.nth Nat.Prime k ∧
    ∀ r : ℕ, Nat.Prime r → r ∣ Nat.factorial n + 1 →
      r = Nat.nth Nat.Prime k ∨ r = Nat.nth Nat.Prime (k + 1)

/-- The original affirmative finiteness target, without a proof assumption. -/
def OriginalQuestion : Prop := Set.Finite {n : ℕ | SupportedFactorial n}

end JSP000878
