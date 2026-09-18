import Mathlib

/-!
# JSP-000598 — central binomial coefficients with equal prime support

The official catalogue asks whether two distinct central binomial coefficients
`(2*n).choose n` can have exactly the same prime divisors.  The proposition
below is the existential reading of that question.
-/

def samePrimeDivisors (a b : ℕ) : Prop := a.primeFactors = b.primeFactors

def JSP000598Statement : Prop :=
  ∃ n m : ℕ, n ≠ m ∧ samePrimeDivisors (Nat.centralBinom n) (Nat.centralBinom m)
