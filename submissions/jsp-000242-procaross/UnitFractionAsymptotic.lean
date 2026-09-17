/-
Released under the Apache 2.0 license. Prepared with AI assistance.
-/
import UnitFractionOptimum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Uniform analytic bounds for the actual finite-set problem of JSP-000242.
The lower construction in Croot's theorem is not assumed or claimed here.
-/

namespace UnitFractionBounds

open scoped BigOperators

/-- The midpoint logarithmic bound is strict, even for a single denominator. -/
theorem reciprocal_lt_log_step {d : ℝ} (hd : 1 / 2 < d) :
    1 / d < Real.log (d + 1 / 2) - Real.log (d - 1 / 2) := by
  have hd0 : 0 < d := by linarith
  have hx0 : 0 < 1 / (2 * d) := by positivity
  have hx1 : 1 / (2 * d) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hpoly : ∀ x : ℝ, 0 ≤ x → x < 1 →
      x + x ^ 3 / 3 ≤ 1 / 2 * Real.log ((1 + x) / (1 - x)) := by
    intro x hx hy
    have hh := Real.sum_range_le_log_div hx hy 2
    norm_num [Finset.sum_range_succ] at hh
    exact hh
  have h := hpoly (1 / (2 * d)) hx0.le hx1
  have heq : (1 + 1 / (2 * d)) / (1 - 1 / (2 * d)) =
      (d + 1 / 2) / (d - 1 / 2) := by
    field_simp
  rw [heq, Real.log_div (by linarith) (by linarith)] at h
  have hc : 0 < (1 / (2 * d)) ^ 3 / 3 := by positivity
  have ht : 2 * (1 / (2 * d)) = 1 / d := by ring
  nlinarith

/-- Consecutive reciprocal envelopes admit a telescoping logarithmic bound. -/
theorem envelope_le_log (k m : ℕ) (hm : 0 < m) :
    (envelope k m : ℝ) ≤
      Real.log ((m : ℝ) + k - 1 / 2) - Real.log ((m : ℝ) - 1 / 2) := by
  induction k generalizing m with
  | zero => simp [envelope]
  | succ k ih =>
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hs := (reciprocal_lt_log_step (d := (m : ℝ)) (by linarith)).le
    have hi := ih (m + 1) (by omega)
    simp only [envelope, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    push_cast at hi ⊢
    have heq : (m : ℝ) + 1 - 1 / 2 = (m : ℝ) + 1 / 2 := by ring
    rw [heq] at hi
    have heq' : (m : ℝ) + 1 + k - 1 / 2 = (m : ℝ) + (k + 1) - 1 / 2 := by ring
    rw [heq'] at hi
    linarith

/-- Positive-length reciprocal envelopes satisfy the strict midpoint bound. -/
theorem envelope_lt_log (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    (envelope k m : ℝ) <
      Real.log ((m : ℝ) + k - 1 / 2) - Real.log ((m : ℝ) - 1 / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := reciprocal_lt_log_step (d := (m : ℝ)) (by linarith)
  have hi := envelope_le_log k (m + 1) (by omega)
  simp only [envelope, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  push_cast at hi ⊢
  have heq : (m : ℝ) + 1 - 1 / 2 = (m : ℝ) + 1 / 2 := by ring
  rw [heq] at hi
  have heq' : (m : ℝ) + 1 + k - 1 / 2 = (m : ℝ) + (k + 1) - 1 / 2 := by ring
  rw [heq'] at hi
  linarith

/-- A uniform bound for every positive rational target and every finite cardinality. -/
theorem minimum_lt_exp_bound (A : Finset ℕ) (k m : ℕ) (r : ℚ)
    (hk : A.card = k) (hm : 0 < m) (hr : 0 < r)
    (hlo : ∀ a ∈ A, m ≤ a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = r) :
    (m : ℝ) < (k : ℝ) / (Real.exp (r : ℝ) - 1) + 1 / 2 := by
  have hk0 : 0 < k := by
    by_contra hn
    have hkz : k = 0 := by omega
    have hA : A = ∅ := Finset.card_eq_zero.mp (hk.trans hkz)
    simp [hA] at hsum
    linarith
  have he := recips_le_envelope A.sort hm A.sortedLT_sort.pairwise
    (fun a ha => hlo a ((Finset.mem_sort (· ≤ ·)).mp ha))
  rw [recips_sort, hsum, Finset.length_sort, hk] at he
  have heR : (r : ℝ) ≤ (envelope k m : ℝ) := by exact_mod_cast he
  have hlog := lt_of_le_of_lt heR (envelope_lt_log k m hk0 hm)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbottom : 0 < (m : ℝ) - 1 / 2 := by linarith
  have htop : 0 < (m : ℝ) + k - 1 / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [← Real.log_div htop.ne' hbottom.ne'] at hlog
  have hexp : Real.exp (r : ℝ) < ((m : ℝ) + k - 1 / 2) / ((m : ℝ) - 1 / 2) :=
    (Real.lt_log_iff_exp_lt (div_pos htop hbottom)).mp hlog
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hepos : 0 < Real.exp (r : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hrR)
  have hmul := (lt_div_iff₀ hbottom).mp hexp
  have hmain : (m : ℝ) - 1 / 2 < (k : ℝ) / (Real.exp (r : ℝ) - 1) := by
    apply (lt_div_iff₀ hepos).mpr
    nlinarith
  linarith

/-- The classical asymptotic upper constant, with an explicit finite error term. -/
theorem attainable_minimum_lt_exp_bound {k m : ℕ} (h : AttainableMinimum k m) :
    (m : ℝ) < (k : ℝ) / (Real.exp 1 - 1) + 1 / 2 := by
  obtain ⟨A, hk, hpos, hsum, hmem, hlo⟩ := h
  simpa using minimum_lt_exp_bound A k m 1 hk (hpos m hmem) (by norm_num) hlo hsum

/-- Explicit convergence rate on the upper side for the actual optimal value. -/
theorem optimalMinimum_ratio_lt (k : ℕ) (hk : 3 ≤ k) :
    (optimalMinimum k : ℝ) / k < 1 / (Real.exp 1 - 1) + 1 / (2 * (k : ℝ)) := by
  have h := attainable_minimum_lt_exp_bound (optimalMinimum_isGreatest k hk).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  apply (div_lt_iff₀ hkR).mpr
  have heq : (k : ℝ) / (Real.exp 1 - 1) + 1 / 2 =
      (1 / (Real.exp 1 - 1) + 1 / (2 * (k : ℝ))) * k := by
    field_simp
  rwa [← heq]

/-- A quantified asymptotic upper bound; it does not assume Croot's construction. -/
theorem optimalMinimum_eventual_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (optimalMinimum k : ℝ) / k < 1 / (Real.exp 1 - 1) + ε := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (2 * ε))
  refine ⟨max K 3, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := (le_max_right K 3).trans hk
  have hKk : (K : ℝ) ≤ k := by exact_mod_cast ((le_max_left K 3).trans hk)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 1 / (2 * (k : ℝ)) < ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * ε)).mp (hK.trans_le hKk)
    nlinarith
  exact (optimalMinimum_ratio_lt k hk3).trans (add_lt_add_right ht _)

end UnitFractionBounds

#print axioms UnitFractionBounds.reciprocal_lt_log_step
#print axioms UnitFractionBounds.envelope_le_log
#print axioms UnitFractionBounds.envelope_lt_log
#print axioms UnitFractionBounds.minimum_lt_exp_bound
#print axioms UnitFractionBounds.attainable_minimum_lt_exp_bound
#print axioms UnitFractionBounds.optimalMinimum_ratio_lt
#print axioms UnitFractionBounds.optimalMinimum_eventual_upper
