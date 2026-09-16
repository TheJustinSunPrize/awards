import Statement

lemma prime_eq_of_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with h1 | hq
  · exact False.elim (hp.ne_one h1)
  · exact hq

lemma not_dvd_44 {p : ℕ} (hp : p.Prime) (hnot : p ≠ 2 ∧ p ≠ 11) : ¬ p ∣ 44 := by
  intro h
  rw [show (44 : ℕ) = 2 * 2 * 11 by norm_num] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact hnot.1 (prime_eq_of_dvd_prime hp (by norm_num) h)
    · exact hnot.1 (prime_eq_of_dvd_prime hp (by norm_num) h)
  · exact hnot.2 (prime_eq_of_dvd_prime hp (by norm_num) h)

lemma not_dvd_175 {p : ℕ} (hp : p.Prime) (hnot : p ≠ 5 ∧ p ≠ 7) : ¬ p ∣ 175 := by
  intro h
  rw [show (175 : ℕ) = 5 * 5 * 7 by norm_num] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact hnot.1 (prime_eq_of_dvd_prime hp (by norm_num) h)
    · exact hnot.1 (prime_eq_of_dvd_prime hp (by norm_num) h)
  · exact hnot.2 (prime_eq_of_dvd_prime hp (by norm_num) h)

lemma c87_prime_dvd {p : ℕ} (hp : p.Prime)
    (hp_cases : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 11) : p ∣ Nat.centralBinom 87 := by
  rcases hp_cases with rfl | rfl | rfl | rfl
  · have hc : Nat.centralBinom 87 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 2 174 < 10)]
    exact Finset.one_le_card.mpr ⟨1, by norm_num⟩
  · have hc : Nat.centralBinom 87 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 5 174 < 10)]
    exact Finset.one_le_card.mpr ⟨3, by norm_num⟩
  · have hc : Nat.centralBinom 87 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 7 174 < 10)]
    exact Finset.one_le_card.mpr ⟨2, by norm_num⟩
  · have hc : Nat.centralBinom 87 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 11 174 < 10)]
    exact Finset.one_le_card.mpr ⟨1, by norm_num⟩

lemma c88_prime_dvd {p : ℕ} (hp : p.Prime)
    (hp_cases : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 11) : p ∣ Nat.centralBinom 88 := by
  rcases hp_cases with rfl | rfl | rfl | rfl
  · have hc : Nat.centralBinom 88 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 2 176 < 10)]
    exact Finset.one_le_card.mpr ⟨4, by norm_num⟩
  · have hc : Nat.centralBinom 88 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 5 176 < 10)]
    exact Finset.one_le_card.mpr ⟨3, by norm_num⟩
  · have hc : Nat.centralBinom 88 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 7 176 < 10)]
    exact Finset.one_le_card.mpr ⟨1, by norm_num⟩
  · have hc : Nat.centralBinom 88 ≠ 0 := Nat.centralBinom_ne_zero _
    apply (hp.dvd_iff_one_le_factorization hc).2
    rw [Nat.centralBinom, Nat.factorization_choose hp (by norm_num)
      (by norm_num : Nat.log 11 176 < 10)]
    exact Finset.one_le_card.mpr ⟨2, by norm_num⟩

lemma central_relation : 44 * Nat.centralBinom (87 + 1) = 175 * Nat.centralBinom 87 := by
  apply Nat.mul_left_cancel (n := 2) (by norm_num)
  calc
    2 * (44 * Nat.centralBinom (87 + 1)) = (87 + 1) * Nat.centralBinom (87 + 1) := by ring
    _ = 2 * (2 * 87 + 1) * Nat.centralBinom 87 := Nat.succ_mul_centralBinom_succ 87
    _ = 2 * (175 * Nat.centralBinom 87) := by ring

lemma same_prime_support :
    (Nat.centralBinom 87).primeFactors = (Nat.centralBinom 88).primeFactors := by
  have hrel : 44 * Nat.centralBinom 88 = 175 * Nat.centralBinom 87 := by
    simpa only [Nat.reduceAdd] using central_relation
  ext p
  constructor
  · intro hp87
    rcases (Nat.mem_primeFactors.mp hp87) with ⟨hpp, hpdiv, _⟩
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpp, ?_, Nat.centralBinom_ne_zero _⟩
    by_cases hc : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 11
    · exact c88_prime_dvd hpp hc
    · have hp2 : p ≠ 2 := fun h => hc (Or.inl h)
      have hp5 : p ≠ 5 := fun h => hc (Or.inr (Or.inl h))
      have hp7 : p ≠ 7 := fun h => hc (Or.inr (Or.inr (Or.inl h)))
      have hp11 : p ≠ 11 := fun h => hc (Or.inr (Or.inr (Or.inr h)))
      have hmul : p ∣ 44 * Nat.centralBinom 88 := by
        rw [hrel]
        exact dvd_mul_of_dvd_right hpdiv 175
      rcases hpp.dvd_mul.mp hmul with h44 | h88
      · exact False.elim (not_dvd_44 hpp ⟨hp2, hp11⟩ h44)
      · exact h88
  · intro hp88
    rcases (Nat.mem_primeFactors.mp hp88) with ⟨hpp, hpdiv, _⟩
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpp, ?_, Nat.centralBinom_ne_zero _⟩
    by_cases hc : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 11
    · exact c87_prime_dvd hpp hc
    · have hp2 : p ≠ 2 := fun h => hc (Or.inl h)
      have hp5 : p ≠ 5 := fun h => hc (Or.inr (Or.inl h))
      have hp7 : p ≠ 7 := fun h => hc (Or.inr (Or.inr (Or.inl h)))
      have hp11 : p ≠ 11 := fun h => hc (Or.inr (Or.inr (Or.inr h)))
      have hmul : p ∣ 175 * Nat.centralBinom 87 := by
        rw [← hrel]
        exact dvd_mul_of_dvd_right hpdiv 44
      rcases hpp.dvd_mul.mp hmul with h175 | h87
      · exact False.elim (not_dvd_175 hpp ⟨hp5, hp7⟩ h175)
      · exact h87

theorem JSP000598.solution : JSP000598Statement := by
  refine ⟨87, 88, by norm_num, ?_⟩
  unfold samePrimeDivisors
  exact same_prime_support

#print axioms JSP000598.solution
