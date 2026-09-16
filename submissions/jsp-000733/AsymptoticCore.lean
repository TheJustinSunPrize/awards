import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
An elementary asymptotic assembly lemma. The assumptions are finite
counting and construction bounds; this file itself makes no claim that
they hold for a particular extremal problem.
-/

open Filter
open scoped Topology

namespace PrimitiveSubsetSums

theorem asymptotic_of_counting_bounds (k : ℕ → ℕ)
    (hupper : ∀ n : ℕ, 0 < n → 2 ^ k n ≤ n * k n + 1)
    (hlower : ∀ n : ℕ, 0 < n → Real.logb 2 (n : ℝ) - 1 < (k n : ℝ)) :
    Tendsto (fun n : ℕ => (k n : ℝ) / Real.logb 2 (n : ℝ)) atTop (𝓝 1) := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogb : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hnat
  have hk : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hlogb (b + 1), eventually_gt_atTop 0]
      with n hbn hn
    have h := hlower n hn
    linarith
  have hkinv : Tendsto (fun n : ℕ => (1 : ℝ) / (k n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hk
  have hkplus : Tendsto (fun n : ℕ => (k n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hk b] with n hn
    linarith
  have hlogsmall :
      Tendsto (fun n : ℕ => Real.log ((k n : ℝ) + 1) / (k n : ℝ))
        atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hkplus
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using h
  have hleft : Tendsto (fun n : ℕ =>
      Real.log 2 - Real.log ((k n : ℝ) + 1) / (k n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa using tendsto_const_nhds.sub hlogsmall
  have hright : Tendsto (fun n : ℕ => Real.log 2 + Real.log 2 / (k n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    have hzero : Tendsto (fun n : ℕ => Real.log 2 / (k n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hk
    simpa using tendsto_const_nhds.add hzero
  have hsandwich : ∀ᶠ n : ℕ in atTop,
      Real.log 2 - Real.log ((k n : ℝ) + 1) / (k n : ℝ) ≤
        Real.log (n : ℝ) / (k n : ℝ) ∧
      Real.log (n : ℝ) / (k n : ℝ) ≤
        Real.log 2 + Real.log 2 / (k n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0, hk.eventually (eventually_gt_atTop 0)]
      with n hn hkn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hknonneg : (0 : ℝ) ≤ k n := by positivity
    have hkp : 0 < (k n : ℝ) + 1 := by positivity
    have hcount : (2 : ℝ) ^ k n ≤ (n : ℝ) * ((k n : ℝ) + 1) := by
      have hcast : (2 : ℝ) ^ k n ≤ (n : ℝ) * (k n : ℝ) + 1 := by
        exact_mod_cast hupper n hn
      nlinarith
    have hlogs := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k n) hcount
    rw [Real.log_pow, Real.log_mul hnreal.ne' hkp.ne'] at hlogs
    constructor
    · calc
        Real.log 2 - Real.log ((k n : ℝ) + 1) / (k n : ℝ) =
            ((k n : ℝ) * Real.log 2 - Real.log ((k n : ℝ) + 1)) / (k n : ℝ) := by
              field_simp
        _ ≤ Real.log (n : ℝ) / (k n : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hkn.le
    · have hlow := hlower n hn
      have hdiv : Real.log (n : ℝ) / Real.log 2 < (k n : ℝ) + 1 := by
        simpa only [Real.logb] using (show Real.logb 2 (n : ℝ) < (k n : ℝ) + 1 by linarith)
      have hlt := (div_lt_iff₀ hc).mp hdiv
      calc
        Real.log (n : ℝ) / (k n : ℝ) ≤
            (((k n : ℝ) + 1) * Real.log 2) / (k n : ℝ) :=
          div_le_div_of_nonneg_right hlt.le hkn.le
        _ = Real.log 2 + Real.log 2 / (k n : ℝ) := by
          field_simp
  have hquot : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (k n : ℝ))
      atTop (𝓝 (Real.log 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
      (hsandwich.mono fun _ h => h.1) (hsandwich.mono fun _ h => h.2)
  have hinverse := hquot.inv₀ hc.ne'
  have hscaled := hinverse.mul_const (Real.log 2)
  convert hscaled using 1
  · ext n
    simp [Real.logb, div_eq_mul_inv, mul_comm, mul_assoc]
  · simp [hc.ne']

end PrimitiveSubsetSums
