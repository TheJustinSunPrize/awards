import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# JSP-000301: consecutive powerful numbers need not include a square

A positive natural number is powerful if the square of each prime divisor
also divides it.  The witnesses are 12167 = 23^3 and
12168 = 2^3 * 3^2 * 13^2.  Both lie strictly between 110^2 and 111^2.
-/

namespace JSP000301

/-- A positive integer whose prime divisors all occur at least twice. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem powerful_12167 : Powerful 12167 := by
  constructor
  · norm_num
  intro p hp hdiv
  have hpow : p ∣ (23 : ℕ) ^ 3 := by
    norm_num
    exact hdiv
  have heq : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hpow)
  subst p
  norm_num

theorem powerful_12168 : Powerful 12168 := by
  constructor
  · norm_num
  intro p hp hdiv
  have hprod : p ∣ (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 := by
    norm_num
    exact hdiv
  rcases hp.dvd_mul.mp hprod with hsmall | h13
  · rcases hp.dvd_mul.mp hsmall with h2 | h3
    · have heq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h2)
      subst p
      norm_num
    · have heq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h3)
      subst p
      norm_num
  · have heq : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h13)
    subst p
    norm_num

/-- There is no natural-number square strictly between successive squares. -/
theorem not_isSquare_between {n a : ℕ}
    (hlo : a * a < n) (hhi : n < (a + 1) * (a + 1)) : ¬ IsSquare n := by
  rintro ⟨k, rfl⟩
  rcases le_or_gt k a with hk | hk
  · exact (not_lt_of_ge (Nat.mul_le_mul hk hk)) hlo
  · have hnext : a + 1 ≤ k := Nat.succ_le_of_lt hk
    exact (not_lt_of_ge (Nat.mul_le_mul hnext hnext)) hhi

theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) := by
  apply not_isSquare_between (a := 110) <;> norm_num

theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) := by
  apply not_isSquare_between (a := 110) <;> norm_num

/-- An explicit counterexample to the claim in JSP-000301. -/
theorem counterexample :
    ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  exact ⟨12167, powerful_12167, powerful_12168,
    not_isSquare_12167, not_isSquare_12168⟩

/-- The universal claim that one of two consecutive powerful numbers
must be a perfect square is false. -/
theorem claim_false :
    ¬ (∀ n : ℕ, Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 powerful_12167 powerful_12168 with hs | hs
  · exact not_isSquare_12167 hs
  · exact not_isSquare_12168 hs

end JSP000301
