import Lean

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace JSP000301

/-- A natural prime: at least two, with no proper divisor other than one. -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Fin p, d.val ∣ p → d.val = 1

instance (p : Nat) : Decidable (Prime p) := by
  unfold Prime
  infer_instance

/-- Connect the finite divisor definition to the usual unbounded one. -/
theorem prime_iff (p : Nat) :
    Prime p ↔ 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p := by
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro d hd
    have hp2 : 2 ≤ p := hp.1
    have hle : d ≤ p := Nat.le_of_dvd (by omega) hd
    by_cases hlt : d < p
    · exact Or.inl (hp.2 ⟨d, hlt⟩ hd)
    · exact Or.inr (by omega)
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro d hd
    rcases hp.2 d.val hd with h | h
    · exact h
    · have := d.isLt
      omega

/-- Positive, with every prime divisor's square dividing the number. -/
def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, Prime p → p ∣ n → p * p ∣ n

def Square (n : Nat) : Prop := ∃ a : Nat, a * a = n

theorem prime_dvd_mul {p a b : Nat} (hp : Prime p) :
    p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro hab
    by_cases ha : p ∣ a
    · exact Or.inl ha
    · have hg := (prime_iff p).mp hp
      rcases hg.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | heq
      · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 hab)
      · have hd := Nat.gcd_dvd_right p a
        rw [heq] at hd
        exact False.elim (ha hd)
  · intro h
    rcases h with ha | hb
    · exact Nat.dvd_mul_right_of_dvd ha b
    · exact Nat.dvd_mul_left_of_dvd hb a

theorem prime_divisor_eq {p q : Nat} (hp : Prime p) (hq : Prime q)
    (hd : p ∣ q) : p = q := by
  rcases ((prime_iff q).mp hq).2 p hd with h | h
  · have := hp.1
    omega
  · exact h

theorem first_powerful : Powerful 12167 := by
  refine ⟨by decide, ?_⟩
  intro p hp hd
  have hf : p ∣ 23 * 23 * 23 := hd
  simp only [prime_dvd_mul hp] at hf
  rcases hf with (h | h) | h
  all_goals
    have heq : p = 23 := prime_divisor_eq hp (by decide +kernel) h
    subst p
    decide

theorem second_powerful : Powerful 12168 := by
  refine ⟨by decide, ?_⟩
  intro p hp hd
  have hf : p ∣ (2 * 2 * 2) * (3 * 3) * (13 * 13) := hd
  simp only [prime_dvd_mul hp] at hf
  rcases hf with (((h | h) | h) | (h | h)) | (h | h)
  all_goals
    first
    | have heq : p = 2 := prime_divisor_eq hp (by decide +kernel) h
      subst p
      decide
    | have heq : p = 3 := prime_divisor_eq hp (by decide +kernel) h
      subst p
      decide
    | have heq : p = 13 := prime_divisor_eq hp (by decide +kernel) h
      subst p
      decide

theorem nonsquare_between {n : Nat}
    (lo : 110 * 110 < n) (hi : n < 111 * 111) : ¬ Square n := by
  rintro ⟨a, ha⟩
  by_cases h : a ≤ 110
  · have hmul : a * a ≤ 110 * 110 := Nat.mul_le_mul h h
    omega
  · have hge : 111 ≤ a := by omega
    have hmul : 111 * 111 ≤ a * a := Nat.mul_le_mul hge hge
    omega

theorem first_not_square : ¬ Square 12167 :=
  nonsquare_between (by decide +kernel) (by decide +kernel)

theorem second_not_square : ¬ Square 12168 :=
  nonsquare_between (by decide +kernel) (by decide +kernel)

theorem counterexample :
    ∃ n : Nat, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ Square n ∧ ¬ Square (n + 1) := by
  exact ⟨12167, by decide, first_powerful, second_powerful,
    first_not_square, second_not_square⟩

theorem original_claim_false :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) →
      Square n ∨ Square (n + 1)) := by
  intro h
  rcases h 12167 (by decide +kernel) first_powerful second_powerful with hsq | hsq
  · exact first_not_square hsq
  · exact second_not_square hsq

#print axioms prime_iff
#print axioms prime_dvd_mul
#print axioms first_powerful
#print axioms second_powerful
#print axioms counterexample
#print axioms original_claim_false

end JSP000301
