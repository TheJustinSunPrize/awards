import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

namespace JSP000971
open scoped ENNReal
noncomputable def returnThreshold (n : ℕ) : ℕ :=
  Nat.ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2) + 1

lemma log_succ_half (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
  have hcast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (by have := Real.log_two_gt_d9; linarith : (1 / 2 : ℝ) ≤ Real.log 2).trans
    (Real.log_le_log (by norm_num) (by linarith))

lemma returnThreshold_ge_two (n : ℕ) (hn : 1 ≤ n) : 2 ≤ returnThreshold n := by
  have hl := log_succ_half n hn
  have hc := Nat.le_ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2)
  have hr : (1 : ℝ) ≤ (Nat.ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2) : ℝ) := by
    nlinarith
  have hi : 1 ≤ Nat.ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2) := by exact_mod_cast hr
  unfold returnThreshold
  omega

lemma geometric_maximum_tail_bound (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℝ≥0∞) * ENNReal.ofReal
      ((1 - 1 / (100 * Real.log ((n : ℝ) + 1))) ^ (returnThreshold n - 1)) ≤
    ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
  let L := Real.log ((n : ℝ) + 1)
  let e := 1 / (100 * L)
  let r := Nat.ceil (300 * L ^ 2)
  have hL : 1 / 2 ≤ L := log_succ_half n hn
  have hLp : 0 < L := by linarith
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    apply (div_le_one (by positivity : 0 < 100 * L)).mpr
    linarith
  have hc : 300 * L ^ 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hprod : 3 * L ≤ e * (r : ℝ) := by
    dsimp [e]
    rw [one_div, mul_comm (100 * L)⁻¹, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 100 * L)).mpr
    nlinarith
  have hpow : (1 - e) ^ r ≤ Real.exp (-(e * (r : ℝ))) := by
    calc
      (1 - e) ^ r ≤ (Real.exp (-e)) ^ r :=
        pow_le_pow_left₀ (sub_nonneg.mpr he1) (Real.one_sub_le_exp_neg e) r
      _ = Real.exp (-(e * (r : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexp : Real.exp (-(3 * L)) = 1 / ((n : ℝ) + 1) ^ 3 := by
    rw [Real.exp_neg, show (3 : ℝ) * L = (3 : ℕ) * L by norm_num,
      Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (n : ℝ) + 1)]
    simp only [one_div]
  have hgeom : (1 - e) ^ r ≤ 1 / ((n : ℝ) + 1) ^ 3 :=
    hpow.trans ((Real.exp_le_exp.mpr (by linarith)).trans_eq hexp)
  change (n + 1 : ℝ≥0∞) * ENNReal.ofReal ((1 - e) ^ r) ≤ _
  calc
    (n + 1 : ℝ≥0∞) * ENNReal.ofReal ((1 - e) ^ r) ≤
        (n + 1 : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 3) := by
      gcongr
    _ = ENNReal.ofReal (((n : ℝ) + 1) * (1 / ((n : ℝ) + 1) ^ 3)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_cast
    _ = ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
      congr 1
      field_simp

lemma summable_inverse_square_succ :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have hs := (summable_nat_add_iff 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one] using hs

lemma below_returnThreshold_log_bound (n m : ℕ) (hn : 2 ≤ n)
    (hm : m < returnThreshold n) :
    (m : ℝ) ≤ 2000 * (Real.log (n : ℝ)) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hl : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) :=
    (by have := Real.log_two_gt_d9; linarith : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hnR)
  have hlu : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have hlnonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
    le_trans (by norm_num) (log_succ_half n (by omega))
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 300 * (Real.log ((n : ℝ) + 1)) ^ 2 by positivity)
  have hm' : m ≤ Nat.ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2) := by
    unfold returnThreshold at hm
    omega
  have hmR : (m : ℝ) ≤ (Nat.ceil (300 * (Real.log ((n : ℝ) + 1)) ^ 2) : ℝ) :=
    by exact_mod_cast hm'
  have hsq : (Real.log ((n : ℝ) + 1)) ^ 2 ≤ 4 * (Real.log (n : ℝ)) ^ 2 := by
    nlinarith
  nlinarith

#print axioms geometric_maximum_tail_bound
#print axioms below_returnThreshold_log_bound
end JSP000971
