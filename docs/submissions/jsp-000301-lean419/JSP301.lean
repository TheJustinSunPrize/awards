import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# JSP-000301: verified formalization of a KNOWN counterexample

Verified on 2026-09-17 with Lean 4.19.0 on Linux x86_64 and mathlib v4.19.0.
The original source passed unchanged before these comment-only status edits.
Both final theorems report only propext, Classical.choice, and Quot.sound.

The pair 12167, 12168 and its factorization are already published in the
Justin Sun Prize catalog. No new mathematical discovery or first-formalization
priority is claimed. This addresses ONLY the catalog's yes/no statement,
not the counting question in Erdos problem 365.

Intended environment: Lean 4.19.0, mathlib v4.19.0.
-/

set_option autoImplicit false

namespace JSP301

/-- A positive integer is powerful when every prime divisor has its square
    dividing the integer. Quantification is over ALL natural primes. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

theorem powerful_left : Powerful 12167 := by
  constructor
  · norm_num
  · intro p hp hd
    have hfactor : (23 : ℕ) ^ 3 = 12167 := by norm_num
    rw [← hfactor] at hd
    have heq : p = 23 :=
      Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hd
    subst p
    norm_num

theorem powerful_right : Powerful 12168 := by
  constructor
  · norm_num
  · intro p hp hd
    have hfactor : (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by norm_num
    rw [← hfactor] at hd
    rcases hp.dvd_mul.mp hd with hsmall | h13
    · rcases hp.dvd_mul.mp hsmall with h2 | h3
      · have heq : p = 2 :=
          Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h2
        subst p
        norm_num
      · have heq : p = 3 :=
          Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h3
        subst p
        norm_num
    · have heq : p = 13 :=
        Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h13
      subst p
      norm_num

/-- Strictly between two adjacent squares there is no natural square.
    The universal square-root quantifier is not replaced by a finite test. -/
private theorem not_square_in_interval {n : ℕ}
    (hlower : 12100 < n) (hupper : n < 12321) : ¬ IsSquare n := by
  intro ⟨k, hk⟩
  by_cases hsmall : k ≤ 110
  · have hbound : k * k ≤ (110 : ℕ) * 110 := Nat.mul_le_mul hsmall hsmall
    norm_num at hbound
    omega
  · have hlarge : 111 ≤ k := by omega
    have hbound : (111 : ℕ) * 111 ≤ k * k := Nat.mul_le_mul hlarge hlarge
    norm_num at hbound
    omega

theorem nonsquare_left : ¬ IsSquare (12167 : ℕ) := by
  exact not_square_in_interval (by norm_num) (by norm_num)

theorem nonsquare_right : ¬ IsSquare (12168 : ℕ) := by
  exact not_square_in_interval (by norm_num) (by norm_num)

/-- The published counterexample, including positivity through Powerful. -/
theorem known_counterexample :
    ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  exact ⟨12167, powerful_left, powerful_right, nonsquare_left, nonsquare_right⟩

/-- The precise yes/no statement in JSP-000301 is false. -/
theorem catalog_statement_false :
    ¬ (∀ n : ℕ, Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases known_counterexample with ⟨n, hn, hnext, hnsq, hnextsq⟩
  rcases h n hn hnext with hs | hs
  · exact hnsq hs
  · exact hnextsq hs

end JSP301

-- Retain these commands to reproduce the axiom audit.
#print axioms JSP301.known_counterexample
#print axioms JSP301.catalog_statement_false
