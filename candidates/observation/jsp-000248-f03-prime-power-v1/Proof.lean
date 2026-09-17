import Statement

open BigOperators

namespace JSP000248

private lemma valuation_scaled_term
    {p a d : ℕ} (hp : p.Prime) (hd : 0 < d) (hlt : d < p ^ a) :
    0 < padicValRat p ((p ^ a : ℚ) / d) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdpow : ¬ p ^ a ∣ d := by
    intro hdiv
    have hle : p ^ a ≤ d := Nat.le_of_dvd hd hdiv
    exact (Nat.not_lt_of_ge hle) hlt
  have hval_lt : padicValNat p d < a := by
    by_contra hnot
    have hle : a ≤ padicValNat p d := Nat.le_of_not_gt hnot
    have hdvd : p ^ a ∣ d := by
      exact (Nat.pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp.two_le) hd.ne').2 hle
    exact hdpow hdvd
  have hval : padicValRat p ((p : ℚ) ^ a / d) = (a : ℤ) - padicValNat p d := by
    rw [padicValRat.div]
    · simp
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    · exact_mod_cast hd.ne'
  rw [hval]
  omega

private lemma positive_sum_scaled
    {p a : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (hs : s.Nonempty) (hpos : ∀ d ∈ s, 0 < d) (hmax : ∀ d ∈ s, d < p ^ a) :
    0 < padicValRat p (∑ d ∈ s, (p ^ a : ℚ) / d) := by
  have : Fact p.Prime := ⟨hp⟩
  let F : ℕ → ℚ := fun i => (p : ℚ) ^ a / (if i = 0 then 1 else i)
  have hpq_pos : 0 < (p : ℚ) ^ a := pow_pos (by exact_mod_cast hp.pos) _
  have hpq_ne : (p : ℚ) ^ a ≠ 0 := ne_of_gt hpq_pos
  have hvalF : padicValRat p (F (p ^ a)) <
      padicValRat p (∑ i ∈ s, F i) := by
    apply padicValRat.lt_sum_of_lt (j := p ^ a) hs
    · intro i hi
      have hi_pos : 0 < i := hpos i hi
      have hi_lt : i < p ^ a := hmax i hi
      have hleft : padicValRat p (F (p ^ a)) = 0 := by
        simp [F, hpq_ne, hp.ne_zero]
      rw [hleft]
      dsimp [F]
      rw [if_neg (Nat.ne_of_gt hi_pos)]
      exact valuation_scaled_term hp hi_pos hi_lt
    · intro i
      dsimp [F]
      by_cases hi : i = 0
      · simpa [hi] using hpq_pos
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
        have hpq : 0 < (p : ℚ) := by exact_mod_cast hp.pos
        positivity
  have hsumF : (∑ i ∈ s, F i) = ∑ i ∈ s, (p : ℚ) ^ a / i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F]
    rw [if_neg (Nat.ne_of_gt (hpos i hi))]
  rw [hsumF] at hvalF
  have hleft : padicValRat p (F (p ^ a)) = 0 := by
    simp [F, hpq_ne, hp.ne_zero]
  rw [hleft] at hvalF
  exact hvalF

/-- A prime power cannot be the largest denominator in a distinct Egyptian-fraction
representation of `1`. -/
theorem prime_power_not_largest
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    PrimePowerNotLargest p a := by
  intro hex
  rcases hex with ⟨s, hsrep, hqmem, hmax⟩
  rcases hsrep with ⟨hpos, hsum⟩
  have : Fact p.Prime := ⟨hp⟩
  let q := p ^ a
  have hqpos : 0 < q := Nat.pow_pos (Nat.zero_lt_of_lt hp.two_le)
  have hqne : q ≠ 0 := Nat.ne_of_gt hqpos
  have htail_pos : ∀ d ∈ s.erase q, 0 < d := by
    intro d hd
    exact hpos d (Finset.mem_of_mem_erase hd)
  have htail_lt : ∀ d ∈ s.erase q, d < q := by
    intro d hd
    have hdle : d ≤ q := hmax d (Finset.mem_of_mem_erase hd)
    have dne : d ≠ q := (Finset.mem_erase.mp hd).1
    exact Nat.lt_of_le_of_ne hdle dne
  have htail_nonempty : (s.erase q).Nonempty := by
    by_contra hempty
    have herase : s.erase q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsingleton : s = {q} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hqmem, by
        intro d hd
        by_contra hdne
        have hderase : d ∈ s.erase q := Finset.mem_erase.mpr ⟨hdne, hd⟩
        rw [herase] at hderase
        simp at hderase⟩
    rw [hsingleton, Finset.sum_singleton] at hsum
    have : (1 : ℚ) / q < 1 := by
      have hqone : (1 : ℚ) < q := by
        dsimp [q]
        have hpa : 1 < p ^ a := by
          exact Nat.one_lt_pow (Nat.ne_of_gt ha) hp.one_lt
        exact_mod_cast hpa
      exact (div_lt_one (by positivity)).2 hqone
    linarith
  have hvaltail : 0 < padicValRat p (∑ d ∈ s.erase q, (q : ℚ) / d) := by
    simpa [q] using positive_sum_scaled hp htail_nonempty htail_pos htail_lt
  have hdecomp :
      (∑ d ∈ s.erase q, (1 : ℚ) / d) + (1 : ℚ) / q = 1 := by
    calc
      (∑ d ∈ s.erase q, (1 : ℚ) / d) + (1 : ℚ) / q =
          ∑ d ∈ s, (1 : ℚ) / d := Finset.sum_erase_add s (fun d => (1 : ℚ) / d) hqmem
      _ = 1 := hsum
  have hscaled :
      1 + ∑ d ∈ s.erase q, (q : ℚ) / d = (q : ℚ) := by
    have hmul := congrArg (fun x : ℚ => (q : ℚ) * x) hdecomp
    rw [mul_add, Finset.mul_sum] at hmul
    have hqdiv : (q : ℚ) * (1 / q) = 1 := by field_simp
    rw [hqdiv] at hmul
    have hterms :
        (∑ d ∈ s.erase q, (q : ℚ) * (1 / d)) =
          ∑ d ∈ s.erase q, (q : ℚ) / d := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hterms] at hmul
    linarith
  have hqval : padicValRat p (q : ℚ) = (a : ℤ) := by
    dsimp [q]
    simp [padicValRat.of_nat]
  have hone_lt : padicValRat p (1 : ℚ) <
      padicValRat p (∑ d ∈ s.erase q, (q : ℚ) / d) := by
    simpa using hvaltail
  have hsumval : padicValRat p (1 + ∑ d ∈ s.erase q, (q : ℚ) / d) = 0 := by
    have htail_sum_pos : 0 < ∑ d ∈ s.erase q, (q : ℚ) / d := by
      apply Finset.sum_pos
      · intro d hd
        have hdpos := htail_pos d hd
        have hqposq : 0 < (q : ℚ) := by exact_mod_cast hqpos
        positivity
      · exact htail_nonempty
    have hne : (1 : ℚ) + ∑ d ∈ s.erase q, (q : ℚ) / d ≠ 0 :=
      ne_of_gt (add_pos (by norm_num) htail_sum_pos)
    simpa using padicValRat.add_eq_of_lt hne (by simp) (ne_of_gt htail_sum_pos) hone_lt
  rw [hscaled] at hsumval
  rw [hqval] at hsumval
  omega

end JSP000248
