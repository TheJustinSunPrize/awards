/-
JSP-001007 / Erdős problem 1202.

Liam Price and GPT-5.4 Pro showed that the half-residue sieve bound fails. This
module proves an explicit elementary lower bound for the number of primes in
`(n, 2n]`, used to build their interval counterexample for every number of
primes. The argument is the Erdős central-binomial estimate, extended from
Bertrand's postulate to a quantitative count. It does not copy upstream Lean
sources.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

open Finset Real

namespace JSP001007

lemma exp_two_thirds_lt_two : exp ((2 : ℝ) / 3) < 2 := by
  have h := exp_bound' (x := (2 : ℝ) / 3) (by norm_num) (by norm_num) (n := 8) (by decide)
  have hsum :
      (∑ m ∈ range 8, ((2 : ℝ) / 3) ^ m / m.factorial) +
        ((2 : ℝ) / 3) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) < 2 := by
    norm_num
  exact h.trans_lt hsum

lemma log_two_gt_two_thirds : (2 / 3 : ℝ) < log 2 := by
  rw [lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  exact exp_two_thirds_lt_two

lemma log_le_four_quarter {y : ℝ} (hy : 0 < y) : log y ≤ 4 * y ^ (1 / 4 : ℝ) := by
  have hy4 : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy _
  have h := log_le_sub_one_of_pos hy4
  rw [log_rpow hy (1 / 4)] at h
  linarith

lemma two_pow_three_quarters_lt : (2 : ℝ) ^ (3 / 4 : ℝ) < 7 / 4 := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  rw [← rpow_lt_rpow_iff (by positivity) (by positivity) h4]
  have hL : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℝ) = 8 := by
    rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hR : ((7 : ℝ) / 4) ^ (4 : ℝ) = 2401 / 256 := by
    norm_num
  rw [hL, hR]
  norm_num

/-- A prime `n < p ≤ 2n` occurs exactly once in the central binomial coefficient. -/
lemma factorization_centralBinom_Ioc {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hlo : n < p) (hhi : p ≤ 2 * n) :
    (Nat.centralBinom n).factorization p = 1 := by
  have hpow : 2 * n < p ^ 2 := by
    have hle : n + 1 ≤ p := by omega
    have hsq : (n + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hle 2
    have hlt : 2 * n < (n + 1) ^ 2 := by
      nlinarith
    exact hlt.trans_le hsq
  have hlog : Nat.log p (2 * n) < 2 := Nat.log_lt_of_lt_pow (by omega : 2 * n ≠ 0) hpow
  rw [Nat.centralBinom_eq_two_mul_choose,
    Nat.factorization_choose hp (by omega : n ≤ 2 * n) hlog]
  have hsub : 2 * n - n = n := by omega
  simp only [hsub]
  have hset :
      ({i ∈ Ico 1 2 | p ^ i ≤ n % p ^ i + n % p ^ i} : Finset ℕ) = {1} := by
    ext i
    simp only [mem_filter, mem_Ico, mem_singleton]
    constructor
    · rintro ⟨⟨hi1, hi2⟩, _⟩
      omega
    · intro hi
      subst hi
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hmod : n % p = n := Nat.mod_eq_of_lt hlo
      simp only [pow_one, hmod]
      omega
  rw [hset, card_singleton]

lemma centralBinom_le_of_few_dyadic_primes (n K : ℕ) (hn : 2 < n)
    (hK : ((Ioc n (2 * n)).filter Nat.Prime).card ≤ K) :
    Nat.centralBinom n ≤ (2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) := by
  classical
  let e : ℕ → ℕ := fun p => (Nat.centralBinom n).factorization p
  have hprod :
      Nat.centralBinom n = ∏ p ∈ range (2 * n + 1), p ^ e p :=
    (Nat.prod_pow_factorization_centralBinom n).symm
  have hdrop :
      ∏ p ∈ range (2 * n + 1), p ^ e p =
        ∏ p ∈ (range (2 * n + 1)).filter (fun p => 0 < e p), p ^ e p := by
    rw [← prod_filter_mul_prod_filter_not (range (2 * n + 1)) (fun p => 0 < e p)]
    have hzero :
        ∏ p ∈ (range (2 * n + 1)).filter (fun p => ¬ 0 < e p), p ^ e p = 1 := by
      refine prod_eq_one fun p hp => ?_
      have he : e p = 0 := by
        have hnot : ¬ 0 < e p := (mem_filter.mp hp).2
        omega
      simp [he]
    rw [hzero, mul_one]
  let support := (range (2 * n + 1)).filter (fun p => 0 < e p)
  let small := support.filter (fun p => p ≤ Nat.sqrt (2 * n))
  let mid := support.filter (fun p => Nat.sqrt (2 * n) < p ∧ p ≤ 2 * n / 3)
  let large := support.filter (fun p => n < p)
  have hcover : ∀ p ∈ support, p ∈ small ∨ p ∈ mid ∨ p ∈ large := by
    intro p hp
    have hps : p ∈ range (2 * n + 1) := (mem_filter.mp hp).1
    have hp' : 0 < e p := (mem_filter.mp hp).2
    have hprime : p.Prime := by
      by_contra hnp
      exact ne_of_gt hp'
        (Nat.factorization_eq_zero_of_not_prime _ hnp)
    have hle2 : p ≤ 2 * n := by
      have : p < 2 * n + 1 := mem_range.mp hps
      omega
    have hnotMid : ¬ (2 * n / 3 < p ∧ p ≤ n) := by
      intro ⟨hgt, hle⟩
      have h3 : 2 * n < 3 * p := by
        have hquot : 2 * n / 3 ≤ p - 1 := Nat.le_sub_one_of_lt hgt
        have hsplit : 2 * n = 3 * (2 * n / 3) + 2 * n % 3 := (Nat.div_add_mod _ _).symm
        have hrem : 2 * n % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      have he0 := Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hle h3
      exact ne_of_gt hp' he0
    by_cases hsqrt : p ≤ Nat.sqrt (2 * n)
    · left
      exact mem_filter.mpr ⟨hp, hsqrt⟩
    · right
      have hsq : Nat.sqrt (2 * n) < p := by omega
      by_cases hleThird : p ≤ 2 * n / 3
      · left
        exact mem_filter.mpr ⟨hp, ⟨hsq, hleThird⟩⟩
      · right
        have hgtn : n < p := by
          by_contra hle
          have hle' : p ≤ n := by omega
          have hgt : 2 * n / 3 < p := by omega
          exact hnotMid ⟨hgt, hle'⟩
        exact mem_filter.mpr ⟨hp, hgtn⟩
  have hdisjSM : Disjoint small mid := by
    rw [disjoint_left]
    intro p hp hm
    have h1 := (mem_filter.mp hp).2
    have h2 := (mem_filter.mp hm).2
    omega
  have hdisjSL : Disjoint small large := by
    rw [disjoint_left]
    intro p hp hl
    have hsqrt : p ≤ Nat.sqrt (2 * n) := (mem_filter.mp hp).2
    have hgt : n < p := (mem_filter.mp hl).2
    have hle : n + 1 ≤ Nat.sqrt (2 * n) := by omega
    have hsq : (n + 1) ^ 2 ≤ 2 * n := (Nat.le_sqrt').mp hle
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have : n ^ 2 + 1 ≤ 0 := by omega
    omega
  have hdisjML : Disjoint mid large := by
    rw [disjoint_left]
    intro p hp hl
    have hle3 : p ≤ 2 * n / 3 := (mem_filter.mp hp).2.2
    have hgt : n < p := (mem_filter.mp hl).2
    have hlt : n < 2 * n / 3 := hgt.trans_le hle3
    have hge : n + 1 ≤ 2 * n / 3 := Nat.succ_le_of_lt hlt
    have hmul : 3 * (n + 1) ≤ 3 * (2 * n / 3) := Nat.mul_le_mul_left _ hge
    have hdiv : 3 * (2 * n / 3) ≤ 2 * n := Nat.mul_div_le (2 * n) 3
    have : 3 * n + 3 ≤ 2 * n := by
      calc
        3 * n + 3 = 3 * (n + 1) := by ring
        _ ≤ 2 * n := hmul.trans hdiv
    omega
  have hunion : small ∪ mid ∪ large = support := by
    ext p
    simp only [mem_union]
    constructor
    · rintro ((hp | hp) | hp)
      · exact (mem_filter.mp hp).1
      · exact (mem_filter.mp hp).1
      · exact (mem_filter.mp hp).1
    · intro hp
      have hmem := hcover p hp
      tauto
  have hsplit :
      ∏ p ∈ support, p ^ e p =
        (∏ p ∈ small, p ^ e p) * (∏ p ∈ mid, p ^ e p) * ∏ p ∈ large, p ^ e p := by
    rw [← hunion, prod_union (disjoint_union_left.mpr ⟨hdisjSL, hdisjML⟩),
      prod_union hdisjSM]
  have hmid : ∏ p ∈ mid, p ^ e p ≤ 4 ^ (2 * n / 3) := by
    have hle : ∏ p ∈ mid, p ^ e p ≤ ∏ p ∈ mid, p := by
      refine prod_le_prod fun p hp => ?_
      have hgt : Nat.sqrt (2 * n) < p := (mem_filter.mp hp).2.1
      have hsq : 2 * n < p ^ 2 := (Nat.sqrt_lt').mp hgt
      have he : e p ≤ 1 := Nat.factorization_choose_le_one hsq
      have hp1 : 1 ≤ p := by
        have hpos : 0 < e p := (mem_filter.mp (mem_filter.mp hp).1).2
        have hprime : p.Prime := by
          by_contra hnp
          exact ne_of_gt hpos
            (Nat.factorization_eq_zero_of_not_prime _ hnp)
        exact hprime.one_lt.le
      exact (Nat.pow_le_pow_right hp1 he).trans (by simp)
    have hprim : ∏ p ∈ mid, p ≤ primorial (2 * n / 3) := by
      have hsub : mid ⊆ (range ((2 * n / 3) + 1)).filter Nat.Prime := by
        intro p hp
        have hsup := (mem_filter.mp hp).1
        have hle3 : p ≤ 2 * n / 3 := (mem_filter.mp hp).2.2
        have hpos : 0 < e p := (mem_filter.mp hsup).2
        have hprime : p.Prime := by
          by_contra hnp
          exact (ne_of_gt hpos)
            (Nat.factorization_eq_zero_of_not_prime _ hnp)
        refine mem_filter.mpr ⟨mem_range.mpr (by omega), hprime⟩
      calc
        ∏ p ∈ mid, p ≤ ∏ p ∈ (range ((2 * n / 3) + 1)).filter Nat.Prime, p :=
          prod_le_prod_of_subset_of_one_le hsub
            fun p hp _ => (mem_filter.mp hp).2.one_lt.le
        _ = primorial (2 * n / 3) := rfl
    exact hle.trans (hprim.trans (primorial_le_four_pow _))
  have hsmall : ∏ p ∈ small, p ^ e p ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
    have hle : ∏ p ∈ small, p ^ e p ≤ ∏ p ∈ small, 2 * n := by
      refine prod_le_prod fun p hp => ?_
      exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    rw [prod_const] at hle
    have hcard : #small ≤ Nat.sqrt (2 * n) := by
      have hsubS : small ⊆ Icc 1 (Nat.sqrt (2 * n)) := by
        intro p hp
        have hleS : p ≤ Nat.sqrt (2 * n) := (mem_filter.mp hp).2
        have hpos : 0 < e p := (mem_filter.mp (mem_filter.mp hp).1).2
        have hprime : p.Prime := by
          by_contra hnp
          exact ne_of_gt hpos
            (Nat.factorization_eq_zero_of_not_prime _ hnp)
        exact mem_Icc.mpr ⟨hprime.one_lt.le, hleS⟩
      have hIcc : #(Icc 1 (Nat.sqrt (2 * n))) = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc]
        omega
      exact (card_le_card hsubS).trans_eq hIcc
    exact hle.trans (Nat.pow_le_pow_right (by omega) hcard)
  have hlarge : ∏ p ∈ large, p ^ e p ≤ (2 * n) ^ K := by
    have hsub : large ⊆ (Ioc n (2 * n)).filter Nat.Prime := by
      intro p hp
      have hsup := (mem_filter.mp hp).1
      have hgt : n < p := (mem_filter.mp hp).2
      have hrange : p ∈ range (2 * n + 1) := (mem_filter.mp hsup).1
      have hle : p ≤ 2 * n := by
        have : p < 2 * n + 1 := mem_range.mp hrange
        omega
      have hpos : 0 < e p := (mem_filter.mp hsup).2
      have hprime : p.Prime := by
        by_contra hnp
        exact ne_of_gt hpos
          (Nat.factorization_eq_zero_of_not_prime _ hnp)
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hgt, hle⟩, hprime⟩
    have hcard : #large ≤ K := (card_le_card hsub).trans hK
    have hle : ∏ p ∈ large, p ^ e p ≤ ∏ p ∈ large, 2 * n := by
      refine prod_le_prod fun p hp => ?_
      have hgt : n < p := (mem_filter.mp hp).2
      have hsup := (mem_filter.mp hp).1
      have hrange : p ∈ range (2 * n + 1) := (mem_filter.mp hsup).1
      have hle2 : p ≤ 2 * n := by
        have : p < 2 * n + 1 := mem_range.mp hrange
        omega
      have hpos : 0 < e p := (mem_filter.mp hsup).2
      have hprime : p.Prime := by
        by_contra hnp
        exact ne_of_gt hpos
          (Nat.factorization_eq_zero_of_not_prime _ hnp)
      have he : e p = 1 := factorization_centralBinom_Ioc hprime (by omega) hgt hle2
      simp [he, hle2]
    rw [prod_const] at hle
    exact hle.trans (Nat.pow_le_pow_right (by omega) hcard)
  have hmul : (2 * n) ^ Nat.sqrt (2 * n) * (2 * n) ^ K =
      (2 * n) ^ (Nat.sqrt (2 * n) + K) := by
    rw [← Nat.pow_add]
  calc
    Nat.centralBinom n = ∏ p ∈ support, p ^ e p := by rw [hprod, hdrop]
    _ = (∏ p ∈ small, p ^ e p) * (∏ p ∈ mid, p ^ e p) * ∏ p ∈ large, p ^ e p := hsplit
    _ ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ K := by
      gcongr
    _ = (2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) := by
      rw [mul_right_comm, hmul]

lemma too_few_primes_false {n : ℕ} (hn : 2 ^ 24 ≤ n)
    (hK : ((Ioc n (2 * n)).filter Nat.Prime).card *
        (16 * (Nat.log 2 (2 * n) + 1)) ≤ n) :
    False := by
  have hn4 : 4 ≤ n := by omega
  have hcentral : 4 ^ n < n * Nat.centralBinom n := Nat.four_pow_lt_mul_centralBinom n hn4
  let K := ((Ioc n (2 * n)).filter Nat.Prime).card
  have hup := centralBinom_le_of_few_dyadic_primes n K (by omega) le_rfl
  have hreal :
      (n : ℝ) * (2 * n : ℝ) ^ (Nat.sqrt (2 * n) + K) * (4 : ℝ) ^ (2 * n / 3) <
        (4 : ℝ) ^ n := by
    let L := Nat.log 2 (2 * n)
    have hloglt : log (2 * (n : ℝ)) < ↑(L + 1) * log 2 := by
      have hnat : 2 * n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) (2 * n)
      have hcast : (2 * n : ℝ) < (2 : ℝ) ^ (L + 1) := by exact_mod_cast hnat
      have hlog := log_lt_log (by positivity) hcast
      rwa [log_pow (2 : ℝ) (L + 1)] at hlog
    have hlog2 : log 2 < 2 := by
      rw [log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
      have h1 : (2 : ℝ) < exp 1 := by
        have h := add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
      exact h1.trans (exp_lt_exp.mpr (by norm_num))
    have hD : (8 : ℝ) * log (2 * (n : ℝ)) < 16 * ↑(L + 1) := by
      have hstep : (8 : ℝ) * log (2 * (n : ℝ)) < 8 * (↑(L + 1) * log 2) :=
        mul_lt_mul_of_pos_left hloglt (by norm_num)
      have hcoef : (8 : ℝ) * log 2 < 16 := by linarith
      calc
        (8 : ℝ) * log (2 * (n : ℝ)) < 8 * (↑(L + 1) * log 2) := hstep
        _ = ↑(L + 1) * (8 * log 2) := by ring
        _ < ↑(L + 1) * 16 := mul_lt_mul_of_pos_left hcoef (by positivity)
        _ = 16 * ↑(L + 1) := by ring
    have hKlog : (K : ℝ) * log (2 * n) ≤ n / 8 := by
      have hKD : (K : ℝ) * (16 * ↑(L + 1)) ≤ n := by
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hK
      have h8 : (8 : ℝ) * log (2 * (n : ℝ)) ≤ 16 * ↑(L + 1) := le_of_lt hD
      have hmul : (K : ℝ) * (8 * log (2 * (n : ℝ))) ≤ (K : ℝ) * (16 * ↑(L + 1)) :=
        mul_le_mul_of_nonneg_left h8 (by exact_mod_cast (Nat.zero_le K))
      have : (K : ℝ) * (8 * log (2 * n)) ≤ n := hmul.trans hKD
      linarith
    have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ √(2 * (n : ℝ)) := by
      simpa [Nat.cast_mul] using (nat_sqrt_le_real_sqrt (a := 2 * n))
    have hlogn : log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) :=
      log_le_four_quarter (by positivity)
    have hlog2n : log (2 * n : ℝ) ≤ 4 * (2 * n : ℝ) ^ (1 / 4 : ℝ) :=
      log_le_four_quarter (by positivity)
    have hsqrtTerm :
        √(2 * n) * log (2 * n) < 7 * (n : ℝ) ^ (3 / 4 : ℝ) := by
      have hpos2n : (0 : ℝ) < 2 * n := by positivity
      calc
        √(2 * n) * log (2 * n)
            ≤ √(2 * n) * (4 * (2 * n : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
        _ = 4 * ((2 * n : ℝ) ^ (1 / 2 : ℝ) * (2 * n : ℝ) ^ (1 / 4 : ℝ)) := by
              rw [Real.sqrt_eq_rpow]; ring
        _ = 4 * (2 * n : ℝ) ^ (3 / 4 : ℝ) := by
              rw [← Real.rpow_add hpos2n]; norm_num
        _ = 4 * ((2 : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) := by
              rw [mul_rpow (by norm_num) (by positivity)]
        _ < 4 * ((7 / 4) * (n : ℝ) ^ (3 / 4 : ℝ)) := by
              gcongr
              exact two_pow_three_quarters_lt
        _ = 7 * (n : ℝ) ^ (3 / 4 : ℝ) := by ring
    have hquarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have hsumlt : log (n : ℝ) + √(2 * n) * log (2 * n) < 11 * (n : ℝ) ^ (3 / 4 : ℝ) := by
      have h1 : log (n : ℝ) ≤ 4 * (n : ℝ) ^ (3 / 4 : ℝ) := by
        exact hlogn.trans (by gcongr)
      linarith [h1, hsqrtTerm]
    have hroot : (64 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hbase : ((2 : ℝ) ^ 24) ^ (1 / 4 : ℝ) = 64 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hncast : (2 ^ 24 : ℝ) ≤ n := by exact_mod_cast hn
      have hmono := Real.rpow_le_rpow (by positivity) hncast (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have : ((2 : ℝ) ^ 24) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
        simpa [Real.rpow_natCast] using hmono
      linarith [hbase, this]
    have hlin : 11 * (n : ℝ) ^ (3 / 4 : ℝ) < (23 / 72) * n := by
      have h64 : (11 : ℝ) < (23 / 72) * 64 := by norm_num
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by positivity
      calc
        (11 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)
            < ((23 / 72) * 64) * (n : ℝ) ^ (3 / 4 : ℝ) := by gcongr
        _ = (23 / 72) * (64 * (n : ℝ) ^ (3 / 4 : ℝ)) := by ring
        _ ≤ (23 / 72) * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hroot hnn
        _ = (23 / 72) * n := by
              rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
              norm_num
    have hcoef : (23 / 72 : ℝ) < log 4 / 3 - 1 / 8 := by
      have hlog4 : (4 / 3 : ℝ) < log 4 := by
        have h := log_two_gt_two_thirds
        have : log 4 = 2 * log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow 2 2]
          norm_cast
        linarith
      have hnum : (4 / 9 : ℝ) - 1 / 8 = 23 / 72 := by norm_num
      linarith
    have hmix : (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) ≤
        √(2 * n) * log (2 * n) + n / 8 := by
      have hlogpos : 0 ≤ log (2 * n : ℝ) := by
        refine log_nonneg ?_
        exact_mod_cast (show 1 ≤ 2 * n by omega)
      have h1 : (Nat.sqrt (2 * n) : ℝ) * log (2 * n) ≤ √(2 * n) * log (2 * n) := by
        gcongr
      linarith [h1, hKlog]
    have hfinal : log (n : ℝ) + (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) <
        n * (log 4 / 3) := by
      have hposn : (0 : ℝ) < n := by positivity
      have hstep1 : log (n : ℝ) + (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) ≤
          log (n : ℝ) + √(2 * n) * log (2 * n) + n / 8 := by
        linarith [hmix]
      have hstep2 : log (n : ℝ) + √(2 * n) * log (2 * n) + n / 8 <
          11 * (n : ℝ) ^ (3 / 4 : ℝ) + n / 8 := by
        linarith [hsumlt]
      have hstep3 : 11 * (n : ℝ) ^ (3 / 4 : ℝ) + n / 8 < (23 / 72) * n + n / 8 := by
        linarith [hlin]
      have hstep4 : (23 / 72) * n + n / 8 < (log 4 / 3 - 1 / 8) * n + n / 8 := by
        have hmul := mul_lt_mul_of_pos_right hcoef hposn
        linarith
      have hstep5 : (log 4 / 3 - 1 / 8) * n + n / 8 = n * (log 4 / 3) := by ring
      exact hstep1.trans_lt (hstep2.trans (hstep3.trans (hstep4.trans_eq hstep5)))
    have hposL : 0 < (n : ℝ) * (2 * n : ℝ) ^ (Nat.sqrt (2 * n) + K) *
        (4 : ℝ) ^ (2 * n / 3) := by positivity
    have hposR : 0 < (4 : ℝ) ^ n := by positivity
    rw [← log_lt_log_iff hposL hposR]
    have hlogL :
        log ((n : ℝ) * (2 * n : ℝ) ^ (Nat.sqrt (2 * n) + K) * (4 : ℝ) ^ (2 * n / 3)) =
          log n + (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) +
            (2 * n / 3 : ℕ) * log 4 := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow (2 * n) (Nat.sqrt (2 * n) + K), log_pow 4 (2 * n / 3)]
      simp [Nat.cast_add, mul_comm, add_assoc, add_comm]
    have hlogR : log ((4 : ℝ) ^ n) = n * log 4 := by
      rw [log_pow 4 n]
    rw [hlogL, hlogR]
    have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ (2 : ℝ) * n / 3 := by
      have hcast := Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := 3)
      calc
        ((2 * n / 3 : ℕ) : ℝ) ≤ (↑(2 * n) : ℝ) / ↑(3 : ℕ) := hcast
        _ = (2 : ℝ) * n / 3 := by simp [Nat.cast_mul]
    have hlog4pos : 0 ≤ log 4 := log_nonneg (by norm_num)
    have htail : ((2 * n / 3 : ℕ) : ℝ) * log 4 ≤ ((2 : ℝ) * n / 3) * log 4 :=
      mul_le_mul_of_nonneg_right hdiv hlog4pos
    have hcomb : log (n : ℝ) + (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) +
        ((2 * n / 3 : ℕ) : ℝ) * log 4 < n * log 4 := by
      have hleft : log (n : ℝ) + (Nat.sqrt (2 * n) + K : ℝ) * log (2 * n) +
          ((2 * n / 3 : ℕ) : ℝ) * log 4 <
          n * (log 4 / 3) + ((2 : ℝ) * n / 3) * log 4 := by
        linarith [hfinal, htail]
      have hid : n * (log 4 / 3) + ((2 : ℝ) * n / 3) * log 4 = n * log 4 := by ring
      exact hleft.trans_eq hid
    exact hcomb
  have hnat :
      n * (2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) < 4 ^ n := by
    exact_mod_cast hreal
  have hle : n * Nat.centralBinom n ≤
      n * (2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) := by
    calc
      n * Nat.centralBinom n
          ≤ n * ((2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3)) :=
        Nat.mul_le_mul_left _ hup
      _ = n * (2 * n) ^ (Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) := by
        rw [← Nat.mul_assoc]
  exact (lt_irrefl _) (hcentral.trans_le (hle.trans hnat.le))

/-- For every `n ≥ 2^24`, `(n, 2n]` contains more than `n / (16 (⌊log₂(2n)⌋ + 1))` primes. -/
theorem many_primes_Ioc {n : ℕ} (hn : 2 ^ 24 ≤ n) :
    n < ((Ioc n (2 * n)).filter Nat.Prime).card * (16 * (Nat.log 2 (2 * n) + 1)) := by
  by_contra h
  exact too_few_primes_false hn (Nat.le_of_not_gt h)

end JSP001007
