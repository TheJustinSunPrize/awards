/- Released under the Apache 2.0 license. Prepared with AI assistance. -/
import UnitFractionCompletion

namespace UnitFractionBounds
open scoped BigOperators

/-- Asymptotically efficient representations along every admissible rational slope. -/
theorem optimalMinimum_blocks (p q : ℕ) (hq : 0 < q)
    (hslope : (Real.exp 1 - 1) * q < p) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ t : ℕ, T ≤ t → q * t ≤ optimalMinimum ((p + 2) * t) := by
  obtain ⟨T, hT⟩ := lcm_dilation_le_factorial (q + p)
  refine ⟨max T 3, le_max_right _ _, ?_⟩
  intro t ht
  have ht3 : 3 ≤ t := (le_max_right T 3).trans ht
  have ht0 : 0 < t := by omega
  have hm : 0 < q * t := Nat.mul_pos hq ht0
  have hm3 : 3 ≤ q * t := by nlinarith
  have hf : Nat.lcmUpto (q * t + p * t) ≤ t.factorial := by
    rw [← Nat.add_mul]
    exact hT t ((le_max_left T 3).trans ht)
  have he : 1 ≤ envelope (p * t) (q * t) := by
    have hl := log_le_envelope (p * t) (q * t) hm
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have htR : (0 : ℝ) < t := by exact_mod_cast ht0
    have hratio : Real.exp 1 < ((q * t : ℕ) + (p * t : ℕ) : ℝ) / (q * t : ℕ) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      push_cast
      nlinarith
    have hlog : 1 < Real.log (((q * t : ℕ) + (p * t : ℕ) : ℝ) / (q * t : ℕ)) :=
      (Real.lt_log_iff_exp_lt (by positivity)).mpr hratio
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have : (1 : ℝ) ≤ (envelope (p * t) (q * t) : ℝ) := (hlog.trans_le hl).le
    exact_mod_cast this
  obtain ⟨A, hlo, hsum, hc⟩ := representation_card_le_of_lcm (p * t) (q * t) t hm hf he
  have hmA := lower_bound_le_card A rfl hm hlo hsum
  have hc3 : 3 ≤ A.card := hm3.trans hmA
  have hp := possible_of_finset A hm rfl hlo hsum
  have hopt := (possible_iff_le_optimalMinimum A.card (q * t) hc3 hm).mp hp
  have hcap : A.card ≤ (p + 2) * t := by nlinarith
  exact hopt.trans (optimalMinimum_mono hc3 hcap)

/-- Padding fills the gaps between block cardinalities, with a finite rounding error. -/
theorem optimalMinimum_lower_from_blocks (p q : ℕ) (hq : 0 < q)
    (hslope : (Real.exp 1 - 1) * q < p) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (q : ℝ) / (p + 2 : ℕ) - (q : ℝ) / k < (optimalMinimum k : ℝ) / k := by
  obtain ⟨T, hT3, hT⟩ := optimalMinimum_blocks p q hq hslope
  refine ⟨(p + 2) * T, ?_⟩
  intro k hk
  let t := k / (p + 2)
  have hd : 0 < p + 2 := by omega
  have hTt : T ≤ t := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hk)
  have ht3 : 3 ≤ t := hT3.trans hTt
  have hkt : (p + 2) * t ≤ k := Nat.mul_div_le k (p + 2)
  have hbase : 3 ≤ (p + 2) * t := by nlinarith
  have hopt : q * t ≤ optimalMinimum k := (hT t hTt).trans (optimalMinimum_mono hbase hkt)
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdR : (0 : ℝ) < (p + 2 : ℕ) := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hround : k < (p + 2) * (t + 1) := by
    have h := Nat.div_add_mod k (p + 2)
    have hrem := Nat.mod_lt k hd
    dsimp [t]
    nlinarith
  have hroundR : (k : ℝ) < (p + 2 : ℕ) * (t + 1 : ℕ) := by exact_mod_cast hround
  have hoptR : (q : ℝ) * t ≤ optimalMinimum k := by exact_mod_cast hopt
  apply (lt_div_iff₀ hkR).mpr
  have heq : ((q : ℝ) / (p + 2 : ℕ) - (q : ℝ) / k) * k =
      (q : ℝ) * k / (p + 2 : ℕ) - q := by field_simp
  rw [heq]
  have hh : (q : ℝ) * k / (p + 2 : ℕ) < (q : ℝ) * t + q := by
    apply (div_lt_iff₀ hdR).mpr
    push_cast at hroundR
    push_cast
    nlinarith
  linarith

/-- The matching lower bound for every sufficiently large cardinality. -/
theorem optimalMinimum_eventual_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      1 / (Real.exp 1 - 1) - ε < (optimalMinimum k : ℝ) / k := by
  let α : ℝ := Real.exp 1 - 1
  have hα : 0 < α := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by norm_num))
  obtain ⟨q, hq⟩ := exists_nat_gt (6 / (ε * α ^ 2))
  have hqR : (0 : ℝ) < q := (by positivity : (0 : ℝ) < 6 / (ε * α ^ 2)).trans hq
  have hq0 : 0 < q := by exact_mod_cast hqR
  let p : ℕ := ⌊α * q⌋₊ + 1
  have hpgt : α * q < (p : ℝ) := by
    dsimp [p]
    exact_mod_cast Nat.lt_floor_add_one (α * q)
  have hple : (p : ℝ) ≤ α * q + 1 := by
    have h := Nat.floor_le (mul_pos hα hqR).le
    dsimp [p]
    push_cast
    linarith
  have hd : (0 : ℝ) < (p + 2 : ℕ) := by positivity
  have hdb : ((p + 2 : ℕ) : ℝ) ≤ α * q + 3 := by push_cast; linarith
  have hda : α * q ≤ (p + 2 : ℕ) := by push_cast; linarith
  have hqε : 6 < ε * α ^ 2 * q := by
    have h := (div_lt_iff₀ (by positivity : 0 < ε * α ^ 2)).mp hq
    nlinarith
  have hprod : 6 < ε * α * (p + 2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hda (mul_pos hε hα).le
    nlinarith
  have hmargin : 1 / α - ε / 2 < (q : ℝ) / (p + 2 : ℕ) := by
    apply (lt_div_iff₀ hd).mpr
    have heq : (1 / α - ε / 2) * (p + 2 : ℕ) =
        (((p + 2 : ℕ) : ℝ) - ε * α * (p + 2 : ℕ) / 2) / α := by field_simp
    rw [heq]
    apply (div_lt_iff₀ hα).mpr
    nlinarith
  obtain ⟨K, hK⟩ := optimalMinimum_lower_from_blocks p q hq0 hpgt
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * (q : ℝ) / ε)
  refine ⟨max K (max J 1), ?_⟩
  intro k hk
  have hKk : K ≤ k := (le_max_left K _).trans hk
  have hJk : J ≤ k := (le_max_left J 1).trans ((le_max_right K _).trans hk)
  have hk0 : 0 < k := by have := (le_max_right J 1).trans ((le_max_right K _).trans hk); omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have herr : (q : ℝ) / k < ε / 2 := by
    apply (div_lt_iff₀ hkR).mpr
    have hJkR : (J : ℝ) ≤ k := by exact_mod_cast hJk
    have h := (div_lt_iff₀ hε).mp (hJ.trans_le hJkR)
    nlinarith
  have hlo := hK k hKk
  change 1 / α - ε < (optimalMinimum k : ℝ) / k
  linarith

/-- Complete asymptotic answer for the uncapped-denominator optimization problem.
This proves convergence, using a factorial remainder construction rather than
assuming the stronger theorem about all denominators lying in a short interval. -/
theorem optimalMinimum_tendsto :
    Filter.Tendsto (fun k : ℕ => (optimalMinimum k : ℝ) / k) Filter.atTop
      (nhds (1 / (Real.exp 1 - 1))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨L, hL⟩ := optimalMinimum_eventual_lower ε hε
  obtain ⟨U, hU⟩ := optimalMinimum_eventual_upper ε hε
  refine ⟨max L U, fun k hk => ?_⟩
  have hl := hL k ((le_max_left L U).trans hk)
  have hu := hU k ((le_max_right L U).trans hk)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end UnitFractionBounds

#print axioms UnitFractionBounds.optimalMinimum_blocks
#print axioms UnitFractionBounds.optimalMinimum_lower_from_blocks
#print axioms UnitFractionBounds.optimalMinimum_eventual_lower
#print axioms UnitFractionBounds.optimalMinimum_tendsto
