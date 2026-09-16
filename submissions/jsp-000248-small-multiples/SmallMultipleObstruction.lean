/-
Copyright (c) 2026 The JSP248 formalization contributors.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0.
Authors: The JSP248 formalization contributors
-/
import PrimePowerObstruction

/-!
# A uniform small-multiple obstruction for largest denominators

This file formalizes an explicit sufficient condition in the exceptional-set
branch of Erdős problem 292 / JSP248. For every positive `m` and `k`, a prime
`p > m * m!` makes `m * p^k` impossible as the largest denominator of a sum of
distinct positive unit fractions equal to one.

The prime-power and small-multiple obstruction context is discussed in
Greg Martin, *Denser Egyptian fractions*, Acta Arith. 95 (2000), pp. 232–233.
The work here is a formalization of an elementary obstruction, not a claim of
new mathematics or of Martin's full exceptional-set counting asymptotic.

The proof groups denominators divisible by `p^k`. After multiplication by
`m! * p^k`, this group is a positive integer strictly below `p`; all remaining
terms have p-adic norm strictly below one. Equality of the original sum with
one would therefore force that positive integer to be divisible by `p`.
-/

namespace JSP248

open scoped BigOperators

/-- A denominator not divisible by the scaling prime power gives a term in
the open p-adic unit ball after scaling. -/
lemma norm_scaled_reciprocal_lt_one
    (p k d : ℕ) [Fact p.Prime] (hd : 0 < d) (hndvd : ¬ p ^ k ∣ d) :
    padicNorm p (((p ^ k : ℕ) : ℚ) / (d : ℚ)) < 1 := by
  have hnotZ : ¬ ((p ^ k : ℕ) : ℤ) ∣ (d : ℤ) := by
    exact_mod_cast hndvd
  have hden : (p : ℚ) ^ (-k : ℤ) < padicNorm p (d : ℚ) := by
    have h := (padicNorm.dvd_iff_norm_le (p := p) (n := k) (z := (d : ℤ))).not.mp
      hnotZ
    simpa only [Int.cast_natCast, not_le] using h
  have hpow : padicNorm p ((p ^ k : ℕ) : ℚ) = (p : ℚ) ^ (-k : ℤ) := by
    rw [padicNorm.eq_zpow_of_nonzero (by
      exact_mod_cast (pow_ne_zero k (Fact.out : p.Prime).ne_zero))]
    simp only [padicValRat.of_nat, padicValNat.prime_pow]
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdenpos : 0 < padicNorm p (d : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hdQ))
  rw [padicNorm.div, hpow]
  exact (div_lt_one hdenpos).2 hden

/-- Uniform obstruction family. The bound `m * m! < p` is a sufficient
condition; this theorem does not assert it is necessary. -/
theorem small_multiple_prime_power_not_largestDenominator
    (m p k : ℕ) (hm : 0 < m) (hp : p.Prime)
    (hsmall : m * m.factorial < p) (hk : 0 < k) :
    ¬ IsLargestDenominator (m * p ^ k) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨S, hS, hmax, hsum⟩
  let q : ℕ := p ^ k
  have hq : 0 < q := pow_pos hp.pos k
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd
    exact (Finset.mem_Icc.mp (hS hd)).1
  have hbound : ∀ d ∈ S, d ≤ m * q := by
    intro d hd
    exact (Finset.mem_Icc.mp (hS hd)).2
  let T := S.filter (fun d => q ∣ d)
  let U := S.filter (fun d => ¬ q ∣ d)
  have hquot : ∀ d ∈ T, 0 < d / q ∧ d / q ≤ m := by
    intro d hd
    obtain ⟨hdS, hdq⟩ := Finset.mem_filter.mp hd
    refine ⟨Nat.div_pos (Nat.le_of_dvd (hpos d hdS) hdq) hq, ?_⟩
    have hmul := Nat.div_mul_cancel hdq
    have hb := hbound d hdS
    nlinarith
  have hTcard : T.card ≤ m := by
    have hc : T.card ≤ (Finset.Icc 1 m).card := by
      apply Finset.card_le_card_of_injOn (fun d => d / q)
      · intro d hd
        exact Finset.mem_Icc.mpr (hquot d hd)
      · intro a ha b hb hab
        have ha' := Nat.div_mul_cancel (Finset.mem_filter.mp ha).2
        have hb' := Nat.div_mul_cancel (Finset.mem_filter.mp hb).2
        calc
          a = (a / q) * q := ha'.symm
          _ = (b / q) * q := congrArg (fun x : ℕ => x * q) hab
          _ = b := hb'
    simpa using hc
  let A : ℕ := ∑ d ∈ T, m.factorial / (d / q)
  have hAupper : A ≤ m * m.factorial := by
    calc
      A ≤ ∑ _d ∈ T, m.factorial := by
        apply Finset.sum_le_sum
        intro d hd
        exact Nat.div_le_self _ _
      _ = T.card * m.factorial := by simp
      _ ≤ m * m.factorial := Nat.mul_le_mul_right _ hTcard
  have hmaxT : m * q ∈ T := by
    exact Finset.mem_filter.mpr ⟨hmax, dvd_mul_left q m⟩
  have hApos : 0 < A := by
    have hdiv : m ∣ m.factorial := Nat.dvd_factorial hm le_rfl
    have htermpos : 0 < m.factorial / m :=
      Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos m) hdiv) hm
    have htermle : m.factorial / ((m * q) / q) ≤ A :=
      Finset.single_le_sum (fun d _ => Nat.zero_le (m.factorial / (d / q))) hmaxT
    have htermle' : m.factorial / m ≤ A := by
      simpa [hq.ne'] using htermle
    exact htermpos.trans_le htermle'
  have htop : (A : ℚ) = ∑ d ∈ T, (m.factorial : ℚ) * ((q : ℚ) / (d : ℚ)) := by
    dsimp [A]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hj := hquot d hd
    have hjdvd : d / q ∣ m.factorial := Nat.dvd_factorial hj.1 hj.2
    have hjQ : ((d / q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hj.1.ne'
    have hmulQ : ((d / q : ℕ) : ℚ) * (q : ℚ) = (d : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel (Finset.mem_filter.mp hd).2
    rw [Nat.cast_div_charZero hjdvd, ← hmulQ]
    field_simp [hjQ, hqQ]
  let B : ℚ := ∑ d ∈ U, (m.factorial : ℚ) * ((q : ℚ) / (d : ℚ))
  have hBnorm : padicNorm p B < 1 := by
    apply padicNorm.sum_lt'
    · intro d hd
      obtain ⟨hdS, hdq⟩ := Finset.mem_filter.mp hd
      have hnorm : padicNorm p ((q : ℚ) / (d : ℚ)) < 1 :=
        norm_scaled_reciprocal_lt_one p k d (hpos d hdS) hdq
      rw [padicNorm.mul]
      exact (mul_le_of_le_one_left (padicNorm.nonneg _) (padicNorm.of_nat _)).trans_lt
        hnorm
    · norm_num
  have hsplit : (A : ℚ) + B = (m.factorial : ℚ) * (q : ℚ) := by
    rw [htop]
    change (∑ d ∈ S.filter (fun d => q ∣ d),
        (m.factorial : ℚ) * ((q : ℚ) / (d : ℚ))) +
      (∑ d ∈ S.filter (fun d => ¬ q ∣ d),
        (m.factorial : ℚ) * ((q : ℚ) / (d : ℚ))) = _
    rw [Finset.sum_filter_add_sum_filter_not]
    calc
      (∑ d ∈ S, (m.factorial : ℚ) * ((q : ℚ) / (d : ℚ))) =
          ((m.factorial : ℚ) * (q : ℚ)) * reciprocalSum S := by
        rw [reciprocalSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = (m.factorial : ℚ) * (q : ℚ) := by rw [hsum, mul_one]
  have hqdiv : p ∣ q := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact ⟨p ^ j, by simp [q, pow_succ, mul_comm]⟩
  have htotalnorm : padicNorm p ((m.factorial : ℚ) * (q : ℚ)) < 1 := by
    rw [padicNorm.mul]
    exact (mul_le_of_le_one_left (padicNorm.nonneg _) (padicNorm.of_nat _)).trans_lt
      ((padicNorm.nat_lt_one_iff q).2 hqdiv)
  have hAnorm : padicNorm p (A : ℚ) < 1 := by
    have hAeq : (A : ℚ) = (m.factorial : ℚ) * (q : ℚ) - B := by linarith [hsplit]
    rw [hAeq]
    exact padicNorm.sub.trans_lt (max_lt htotalnorm hBnorm)
  have hpA : p ∣ A := (padicNorm.nat_lt_one_iff A).1 hAnorm
  exact (not_lt_of_ge (Nat.le_of_dvd hApos hpA)) (hAupper.trans_lt hsmall)

end JSP248

#print axioms JSP248.norm_scaled_reciprocal_lt_one
#print axioms JSP248.small_multiple_prime_power_not_largestDenominator
