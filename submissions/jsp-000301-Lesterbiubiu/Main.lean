import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace JSP000301

/-- A natural number `n` is *powerful* when every prime divisor `p` of `n`
occurs to an exponent of at least two, i.e. `p * p ∣ n`. -/
def IsPowerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p * p ∣ n

/-! ### The two numbers are consecutive -/

theorem consecutive : 12167 + 1 = 12168 := by norm_num

/-! ### `12167` is powerful -/

theorem powerful_12167 : IsPowerful 12167 := by
  intro p hp hpdvd
  have hfac : (12167 : ℕ) = 23 ^ 3 := by norm_num
  rw [hfac] at hpdvd
  have hp23 : p ∣ 23 := hp.dvd_of_dvd_pow hpdvd
  have hp_eq : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23)).mp hp23
  subst hp_eq
  norm_num

/-! ### `12168` is powerful -/

theorem powerful_12168 : IsPowerful 12168 := by
  intro p hp hpdvd
  have hfac : (12168 : ℕ) = 2 ^ 3 * (3 ^ 2 * 13 ^ 2) := by norm_num
  rw [hfac] at hpdvd
  have hsplit : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 13 := by
    rcases hp.dvd_mul.mp hpdvd with h2 | hrest
    · exact Or.inl (hp.dvd_of_dvd_pow h2)
    · rcases hp.dvd_mul.mp hrest with h3 | h13
      · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inr (hp.dvd_of_dvd_pow h13))
  rcases hsplit with h2 | h3 | h13
  · have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2
    subst hp2
    norm_num
  · have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
    subst hp3
    norm_num
  · have hp13 : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp h13
    subst hp13
    norm_num

/-! ### Neither number is a perfect square -/

/-- A natural number strictly between `m * m` and `(m + 1) * (m + 1)` is not a
perfect square. -/
theorem not_isSquare_of_between {n m : ℕ} (hlo : m * m < n)
    (hhi : n < (m + 1) * (m + 1)) : ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hkmul : k * k = n := hk.symm
  have hk_le : k ≤ m := by
    by_contra h
    push Not at h
    nlinarith
  have hk_ge : m + 1 ≤ k := by
    by_contra h
    push Not at h
    nlinarith
  omega

theorem not_isSquare_12167 : ¬ IsSquare 12167 :=
  not_isSquare_of_between (by norm_num : 110 * 110 < 12167)
    (by norm_num : 12167 < 111 * 111)

theorem not_isSquare_12168 : ¬ IsSquare 12168 :=
  not_isSquare_of_between (by norm_num : 110 * 110 < 12168)
    (by norm_num : 12168 < 111 * 111)

/-! ### The counterexample and the answer to the problem -/

/-- The explicit witness: two consecutive powerful numbers, neither a square. -/
theorem jsp_000301_witness :
    IsPowerful 12167 ∧ IsPowerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 :=
  ⟨powerful_12167, powerful_12168, not_isSquare_12167, not_isSquare_12168⟩

/-- **JSP-000301.** It is *not* the case that among two consecutive powerful
positive integers at least one is a perfect square. -/
theorem jsp_000301 :
    ¬ (∀ n : ℕ, 0 < n → IsPowerful n → IsPowerful (n + 1) →
        IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  have h12168 : IsPowerful (12167 + 1) := by
    rw [consecutive]
    exact powerful_12168
  rcases h 12167 (by norm_num) powerful_12167 h12168 with hs | hs
  · exact not_isSquare_12167 hs
  · rw [consecutive] at hs
    exact not_isSquare_12168 hs

/-! ### The same counterexample, stated existentially -/

/-- The counterexample stated positively: there *exist* two consecutive powerful
positive integers of which neither is a perfect square.  This is the form that
matches the problem's "must at least one be a square?" question most directly:
it exhibits the witness rather than refuting the universal claim.  It is
classically equivalent to `jsp_000301` above. -/
theorem jsp_000301_exists :
    ∃ a b : ℕ, 0 < a ∧ IsPowerful a ∧ IsPowerful b ∧ b = a + 1 ∧
      ¬ IsSquare a ∧ ¬ IsSquare b :=
  ⟨12167, 12168, by norm_num, powerful_12167, powerful_12168, consecutive.symm,
    not_isSquare_12167, not_isSquare_12168⟩

end JSP000301
