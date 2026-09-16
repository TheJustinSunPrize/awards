import Maximum
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter

namespace Erdos882Trial

private theorem log_two_four : Real.logb 2 4 = 2 := by
  have h := Real.logb_pow 2 2 2
  norm_num at h ⊢
  exact h

private theorem log_two_thirtytwo : Real.logb 2 32 = 5 := by
  have h := Real.logb_pow 2 2 5
  norm_num at h ⊢
  exact h

theorem five_le_log_two {n : ℕ} (hn : 32 ≤ n) : 5 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (show (0 : ℝ) < 32 by norm_num) (show (32 : ℝ) ≤ n by exact_mod_cast hn)
  rwa [log_two_thirtytwo] at h

/-- The finite bound with constant 32 yields the half-log-log secondary term. -/
theorem logarithmic_bound_of_squared {n k : ℕ}
    (hn : 32 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hpow : 4 ^ k ≤ 32 * k * n ^ 2) :
    (k : ℝ) ≤ Real.logb 2 (n : ℝ) +
      (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpowR : (4 : ℝ) ^ k ≤ 32 * (k : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hpow
  have hlogs := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (show (0 : ℝ) < 4 ^ k by positivity) hpowR
  rw [Real.logb_pow,
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by norm_num) (ne_of_gt hkpos),
    Real.logb_pow, log_two_four, log_two_thirtytwo] at hlogs
  have hlogkn := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    hkpos (show (k : ℝ) ≤ n by exact_mod_cast hkn)
  have hx := five_le_log_two hn
  have hrough : (k : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by
    norm_num at hlogs
    linarith
  have hlogrough := Real.logb_le_logb_of_le (b := 2) (by norm_num) hkpos hrough
  rw [Real.logb_mul (by norm_num) (by linarith : Real.logb 2 (n : ℝ) ≠ 0),
    Real.logb_self_eq_one (by norm_num)] at hlogrough
  norm_num at hlogs
  linarith

/-- The real logarithmic bound under the original primitivity condition, including small sets. -/
theorem admissible_refined_upper_bound {n : ℕ} {A : Finset ℕ}
    (hn : 32 ≤ n) (hA : Admissible n A) :
    (A.card : ℝ) ≤ Real.logb 2 (n : ℝ) +
      (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + 3 := by
  by_cases hk : 2 ≤ A.card
  · exact logarithmic_bound_of_squared hn hk (admissible_card_le hA)
      (admissible_squared_bound hA hk)
  · have hc : (A.card : ℝ) ≤ 1 := by exact_mod_cast (show A.card ≤ 1 by omega)
    have hx := five_le_log_two hn
    have hlogx := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ Real.logb 2 (n : ℝ) by linarith)
    simp only [Real.logb_one] at hlogx
    linarith

/-- The explicit constant and threshold bound for the actual maximum cardinality. -/
theorem maximumSize_refined_upper_bound {n : ℕ} (hn : 32 ≤ n) :
    (maximumSize n : ℝ) ≤ Real.logb 2 (n : ℝ) +
      (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + 3 := by
  obtain ⟨A, hA, heq⟩ := maximumSize_attained n
  rw [← heq]
  exact admissible_refined_upper_bound hn hA

/-- The full eventual refined upper bound with an existential constant. -/
theorem refined_upper_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (maximumSize n : ℝ) ≤ Real.logb 2 (n : ℝ) +
        (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + C := by
  refine ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop (32 : ℕ)] with n hn
  exact maximumSize_refined_upper_bound hn

end Erdos882Trial

#check @Erdos882Trial.refined_upper_bound
#print axioms Erdos882Trial.maximumSize_refined_upper_bound
#print axioms Erdos882Trial.refined_upper_bound
