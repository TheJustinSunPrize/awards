/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 James-16.
Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.
The definitions and final theorem statement are adapted from Formal Conjectures.
The proofs in this file are new and were prepared with OpenAI Codex assistance.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Steinerberger's prime-divisibility criterion for Erdős 291 / JSP-000247.
The mathematical criterion is recorded at https://www.erdosproblems.com/291. -/
namespace Erdos291Criterion
open Finset

def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm (fun x ↦ x)
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, L n / i

theorem L_pos (n : ℕ) : 0 < L n := Nat.lcmUpto_pos n

theorem dvd_L {i n : ℕ} (hi : i ∈ Finset.Icc 1 n) : i ∣ L n := Finset.dvd_lcm hi

theorem factorization_L (n p : ℕ) (hp : p.Prime) :
    (L n).factorization p = Nat.log p n := Nat.factorization_lcmUpto n hp

theorem harmonic_eq (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / i) = (a n : ℚ) / L n := by
  have hL : (L n : ℚ) ≠ 0 := by exact_mod_cast (L_pos n).ne'
  apply (eq_div_iff hL).2
  rw [Finset.sum_mul]
  unfold a
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  rw [Nat.cast_div (dvd_L hi) (by exact_mod_cast hi0)]
  ring

/-- Reducing a fraction with denominator prime to p preserves p-divisibility
of its numerator. -/
theorem numerator_criterion (A B p : ℕ) (hp : p.Prime) (hB : 0 < B)
    (hpB : ¬p ∣ B) :
    p ∣ A ↔ (p : ℤ) ∣ ((A : ℚ) / B).num := by
  let q : ℚ := (A : ℚ) / B
  have hcross : (q.num : ℚ) * B = (A : ℚ) * q.den := by
    apply (div_eq_div_iff (by exact_mod_cast q.den_ne_zero)
      (by exact_mod_cast hB.ne')).mp
    exact q.num_div_den
  have hcrossZ : q.num * (B : ℤ) = (A : ℤ) * q.den := by exact_mod_cast hcross
  have hcrossN : q.num.natAbs * B = A * q.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hcrossZ
  have hdB : q.den ∣ B := q.reduced.symm.dvd_of_dvd_mul_left (by
    rw [hcrossN]
    exact dvd_mul_left _ _)
  have hpd : ¬p ∣ q.den := fun h ↦ hpB (h.trans hdB)
  change p ∣ A ↔ (p : ℤ) ∣ q.num
  rw [Int.natCast_dvd]
  constructor
  · intro h
    have hx : p ∣ q.num.natAbs * B := by rw [hcrossN]; exact dvd_mul_of_dvd_left h _
    exact (hp.dvd_mul.mp hx).resolve_right hpB
  · intro h
    have hx : p ∣ A * q.den := by rw [← hcrossN]; exact dvd_mul_of_dvd_left h _
    exact (hp.dvd_mul.mp hx).resolve_right hpd

theorem sum_multiples (n P : ℕ) (hP : 0 < P) :
    (∑ i ∈ (Finset.Icc 1 n).filter (fun i ↦ P ∣ i), L n / i) =
      ∑ j ∈ Finset.Icc 1 (n / P), L n / (P * j) := by
  symm
  refine Finset.sum_bij (fun j _ ↦ P * j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by exact Nat.mul_pos hP (by omega), ?_⟩, dvd_mul_right _ _⟩
    have := (Nat.le_div_iff_mul_le hP).mp hj2
    simpa only [Nat.mul_comm] using this
  · intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hP hij
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi, ⟨j, rfl⟩⟩
    rcases Finset.mem_Icc.mp hi with ⟨hi1, hi2⟩
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      have : j = 0 := by omega
      simp [this] at hi1
    · apply (Nat.le_div_iff_mul_le hP).mpr
      simpa only [Nat.mul_comm] using hi2
  · intro j hj
    rfl

theorem small_L_dvd_quotient (n P : ℕ) (hP : 0 < P) (hPL : P ∣ L n) :
    L (n / P) ∣ L n / P := by
  apply Finset.lcm_dvd
  intro j hj
  apply (Nat.dvd_div_iff_mul_dvd hPL).2
  apply dvd_L
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
  refine Finset.mem_Icc.mpr ⟨by exact Nat.mul_pos hP (by omega), ?_⟩
  have := (Nat.le_div_iff_mul_le hP).mp hj2
  simpa only [Nat.mul_comm] using this

theorem sum_multiples_factor (n P : ℕ) (hP : 0 < P) (hPL : P ∣ L n) :
    (∑ i ∈ (Finset.Icc 1 n).filter (fun i ↦ P ∣ i), L n / i) =
      (L n / P / L (n / P)) * a (n / P) := by
  rw [sum_multiples n P hP, a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Nat.div_div_eq_div_mul]
  conv_lhs => rw [← Nat.div_mul_cancel (small_L_dvd_quotient n P hP hPL)]
  exact Nat.mul_div_assoc _ (dvd_L hj)

theorem prime_power_dvd_L (n p : ℕ) (hp : p.Prime) :
    p ^ Nat.log p n ∣ L n := by
  apply (hp.pow_dvd_iff_le_factorization (L_pos n).ne').mpr
  rw [factorization_L n p hp]

theorem prime_not_dvd_power_quotient (n p : ℕ) (hp : p.Prime) :
    ¬p ∣ L n / p ^ Nat.log p n := by
  have hP : 0 < p ^ Nat.log p n := pow_pos hp.pos _
  have hd := prime_power_dvd_L n p hp
  have hq : L n / p ^ Nat.log p n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (L_pos n) hd) hP).ne'
  rw [hp.dvd_iff_one_le_factorization hq, Nat.factorization_div hd,
    Finsupp.tsub_apply, factorization_L n p hp, hp.factorization_pow,
    Finsupp.single_eq_same]
  omega

theorem prime_dvd_other_quotient (n p i : ℕ) (hp : p.Prime)
    (hi : i ∈ Finset.Icc 1 n) (hnot : ¬p ^ Nat.log p n ∣ i) : p ∣ L n / i := by
  have hi0 : 0 < i := (Finset.mem_Icc.mp hi).1
  have hd := dvd_L hi
  have hq : L n / i ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (L_pos n) hd) hi0).ne'
  have hv : i.factorization p < Nat.log p n := by
    apply Nat.lt_of_not_ge
    intro h
    exact hnot ((hp.pow_dvd_iff_le_factorization hi0.ne').mpr h)
  rw [hp.dvd_iff_one_le_factorization hq, Nat.factorization_div hd,
    Finsupp.tsub_apply, factorization_L n p hp]
  omega

theorem prime_not_dvd_small_L (k p : ℕ) (hp : p.Prime) (hk : k < p) :
    ¬p ∣ L k := by
  rw [hp.dvd_iff_one_le_factorization (L_pos k).ne', factorization_L k p hp,
    Nat.log_of_lt hk]
  omega

/-- Divisibility of the unreduced numerator is determined by the leading base-p digit. -/
theorem leading_digit_reduction (n p : ℕ) (hp : p.Prime) :
    p ∣ a n ↔ p ∣ a (n / p ^ Nat.log p n) := by
  let P := p ^ Nat.log p n
  have hP : 0 < P := pow_pos hp.pos _
  have hPL : P ∣ L n := prime_power_dvd_L n p hp
  have hsmall : L (n / P) ∣ L n / P := small_L_dvd_quotient n P hP hPL
  have hw : ¬p ∣ L n / P / L (n / P) := by
    intro h
    exact prime_not_dvd_power_quotient n p hp (h.trans (Nat.div_dvd_of_dvd hsmall))
  have hother : p ∣ ∑ i ∈ (Finset.Icc 1 n).filter (fun i ↦ ¬P ∣ i), L n / i := by
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨hi, hnot⟩ := Finset.mem_filter.mp hi
    exact prime_dvd_other_quotient n p i hp hi hnot
  have hsplit :
      (∑ i ∈ (Finset.Icc 1 n).filter (fun i ↦ P ∣ i), L n / i) +
      (∑ i ∈ (Finset.Icc 1 n).filter (fun i ↦ ¬P ∣ i), L n / i) = a n :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit, ← Nat.dvd_add_iff_left hother, sum_multiples_factor n P hP hPL,
    hp.dvd_mul]
  exact or_iff_right hw

/-- Steinerberger's necessary and sufficient criterion, for every prime p ≤ n. -/
theorem steinerberger_generalization (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    let k := n / p ^ Nat.log p n
    p ∣ Nat.gcd (a n) (L n) ↔
      (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num := by
  dsimp only
  have hdL : p ∣ L n := dvd_L (Finset.mem_Icc.mpr ⟨hp.one_le, hpn⟩)
  have hP : 0 < p ^ Nat.log p n := pow_pos hp.pos _
  have hk : n / p ^ Nat.log p n < p := by
    apply (Nat.div_lt_iff_lt_mul hP).mpr
    simpa only [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self hp.one_lt n
  rw [Nat.dvd_gcd_iff, and_iff_left hdL, leading_digit_reduction n p hp,
    harmonic_eq]
  exact numerator_criterion _ _ p hp (L_pos _) (prime_not_dvd_small_L _ p hp hk)

end Erdos291Criterion
