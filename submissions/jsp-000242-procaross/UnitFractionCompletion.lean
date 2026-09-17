/- Released under the Apache 2.0 license. Prepared with AI assistance. -/
import UnitFractionRemainder
import UnitFractionAsymptotic
import Mathlib.NumberTheory.Chebyshev

namespace UnitFractionBounds
open scoped BigOperators

theorem small_target_short (r : ℚ) (m n : ℕ) (hm : 0 < m)
    (hr : 0 ≤ r) (hsmall : r < 1 / (m : ℚ)) (hden : r.den ≤ n.factorial) :
    ∃ l : List ℕ, l.Pairwise (· < ·) ∧ (∀ d ∈ l, m < d) ∧
      recips l = r ∧ l.length ≤ 2 * n := by
  have hnum : (r.num.natAbs : ℚ) = r.num := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hr))
    simpa only [Int.cast_natCast] using h
  have heq : (r.num.natAbs : ℚ) / r.den = r := by rw [hnum, Rat.num_div_den]
  have hr1 : r < 1 := hsmall.trans_le (by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) (by exact_mod_cast hm))
  have hn : r.num.natAbs < r.den := by
    have h : (r.num.natAbs : ℚ) < r.den := (div_lt_one (by exact_mod_cast r.pos)).mp (by rwa [heq])
    exact_mod_cast h
  obtain ⟨A, hp, hs, hc⟩ := egyptian_length_factorial r.num.natAbs r.den n hn hden
  have hs' : (∑ d ∈ A, (1 : ℚ) / d) = r := hs.trans heq
  have hlo : ∀ d ∈ A, m < d := by
    intro d hd
    have hu : (1 : ℚ) / d ≤ r := by
      rw [← hs']
      exact Finset.single_le_sum (f := fun e : ℕ => (1 : ℚ) / e) (fun e _ => by positivity) hd
    have hlt := hu.trans_lt hsmall
    exact_mod_cast (one_div_lt_one_div (by exact_mod_cast hp d hd) (by exact_mod_cast hm)).mp hlt
  exact ⟨A.sort, A.sortedLT_sort.pairwise,
    fun d hd => hlo d ((Finset.mem_sort (· ≤ ·)).mp hd),
    by rw [recips_sort, hs'], by simpa using hc⟩

/-- Finish a harmonic prefix with at most twice the factorial index many terms. -/
theorem short_representation_of_envelope (k m L n : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hf : L ≤ n.factorial) (r : ℚ) (hr : 0 ≤ r) (hrd : r.den ∣ L)
    (hdiv : ∀ d : ℕ, m ≤ d → d < m + k → d ∣ L) (he : r ≤ envelope k m) :
    ∃ l : List ℕ, l.Pairwise (· < ·) ∧ (∀ d ∈ l, m ≤ d) ∧
      recips l = r ∧ l.length ≤ k + 2 * n := by
  induction k generalizing m r with
  | zero =>
    have hz : r = 0 := le_antisymm he hr
    exact ⟨[], by simp, by simp, by simp [hz], by simp⟩
  | succ k ih =>
    by_cases hsmall : r < 1 / (m : ℚ)
    · obtain ⟨l, hs, hlo, hsum, hlen⟩ := small_target_short r m n hm hr hsmall ((Nat.le_of_dvd hL hrd).trans hf)
      exact ⟨l, hs, fun d hd => (hlo d hd).le, hsum, by omega⟩
    · have hnonneg : 0 ≤ r - 1 / (m : ℚ) := sub_nonneg.mpr (le_of_not_gt hsmall)
      have htail : r - 1 / (m : ℚ) ≤ envelope k (m + 1) := by
        change r ≤ 1 / (m : ℚ) + envelope k (m + 1) at he
        linarith
      have hmd : (1 / (m : ℚ)).den ∣ L := by
        have heq : (1 / (m : ℚ)).den = m := by
          rw [one_div, Rat.den_inv_of_ne_zero (by exact_mod_cast hm.ne')]
          simp
        rw [heq]
        exact hdiv m le_rfl (by omega)
      have hd : (r - 1 / (m : ℚ)).den ∣ L :=
        (Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd hrd hmd)
      obtain ⟨l, hs, hlo, hsum, hlen⟩ := ih (m + 1) (by omega) _ hnonneg hd
        (fun d hd hu => hdiv d (by omega) (by omega)) htail
      refine ⟨m :: l, List.pairwise_cons.mpr ⟨fun d hd => by have := hlo d hd; omega, hs⟩, ?_, ?_, ?_⟩
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact le_rfl
        · exact (Nat.le_succ m).trans (hlo d hd)
      · rw [recips_cons, hsum]; ring
      · simp only [List.length_cons]; omega

/-- A finite sufficient condition for an exact representation with a short tail. -/
theorem representation_card_le_of_lcm (k m n : ℕ) (hm : 0 < m)
    (hf : Nat.lcmUpto (m + k) ≤ n.factorial) (he : 1 ≤ envelope k m) :
    ∃ A : Finset ℕ, (∀ d ∈ A, m ≤ d) ∧
      (∑ d ∈ A, (1 : ℚ) / d) = 1 ∧ A.card ≤ k + 2 * n := by
  obtain ⟨l, hs, hlo, hsum, hlen⟩ := short_representation_of_envelope k m
    (Nat.lcmUpto (m + k)) n hm (Nat.lcmUpto_pos _) hf 1 (by norm_num)
    (by simp) (fun d hd hu => by
      apply Finset.dvd_lcm
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩) he
  refine ⟨l.toFinset, fun d hd => hlo d (List.mem_toFinset.mp hd), ?_, ?_⟩
  · rw [List.sum_toFinset _ hs.nodup]; exact hsum
  · rwa [List.toFinset_card_of_nodup hs.nodup]

/-- The elementary integral lower bound for the harmonic prefix. -/
theorem log_le_envelope (k m : ℕ) (hm : 0 < m) :
    Real.log ((m : ℝ) + k) - Real.log m ≤ (envelope k m : ℝ) := by
  induction k generalizing m with
  | zero => simp [envelope]
  | succ k ih =>
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hs : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / (m : ℝ) := by
      rw [← Real.log_div (by positivity) hmR.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < m + 1) hmR)
      have heq : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
      rwa [heq] at h
    have hi := ih (m + 1) (by omega)
    simp only [envelope, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    push_cast at hi ⊢
    have heq : (m : ℝ) + 1 + k = m + (k + 1) := by ring
    rw [heq] at hi
    linarith

/-- For each fixed dilation, factorials eventually dominate the required common denominator. -/
theorem lcm_dilation_le_factorial (D : ℕ) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → Nat.lcmUpto (D * t) ≤ t.factorial := by
  let C : ℝ := (Real.log 4 + 4) * D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨A, hA⟩ := exists_nat_ge (Real.exp (2 * C))
  have hA0 : 0 < A := by
    have h : (0 : ℝ) < A := (Real.exp_pos _).trans_le hA
    exact_mod_cast h
  have hlogA : 2 * C ≤ Real.log A := by
    simpa using Real.log_le_log (Real.exp_pos _) hA
  refine ⟨2 * A, fun t ht => ?_⟩
  have hAt : A ≤ t := by omega
  have hpow : A ^ (t - A) ≤ t.factorial := by
    have h := Nat.factorial_mul_pow_sub_le_factorial hAt
    have hpos := Nat.factorial_pos A
    nlinarith
  have hpR : (0 : ℝ) < (A : ℝ) ^ (t - A) := by positivity
  have hlogF : (t - A : ℕ) * Real.log A ≤ Real.log (t.factorial : ℝ) := by
    have h := Real.log_le_log hpR (show (A : ℝ) ^ (t - A) ≤ (t.factorial : ℝ) by exact_mod_cast hpow)
    simpa [Real.log_pow] using h
  have hhalf : (t : ℝ) ≤ 2 * (t - A : ℕ) := by exact_mod_cast (by omega : t ≤ 2 * (t - A))
  have hCF : C * t ≤ Real.log (t.factorial : ℝ) := by
    have hn : (0 : ℝ) ≤ (t - A : ℕ) := by positivity
    nlinarith
  have hLC := Chebyshev.psi_le_const_mul_self (x := (D * t : ℕ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hLC
  have hlog : Real.log (Nat.lcmUpto (D * t) : ℝ) ≤ Real.log (t.factorial : ℝ) := by
    dsimp [C] at hCF
    push_cast at hLC
    nlinarith
  have hLpos : (0 : ℝ) < Nat.lcmUpto (D * t) := by exact_mod_cast Nat.lcmUpto_pos _
  have hFpos : (0 : ℝ) < t.factorial := by positivity
  exact_mod_cast (Real.log_le_log_iff hLpos hFpos).mp hlog

end UnitFractionBounds

#print axioms UnitFractionBounds.small_target_short
#print axioms UnitFractionBounds.short_representation_of_envelope
#print axioms UnitFractionBounds.representation_card_le_of_lcm
#print axioms UnitFractionBounds.log_le_envelope
#print axioms UnitFractionBounds.lcm_dilation_le_factorial
