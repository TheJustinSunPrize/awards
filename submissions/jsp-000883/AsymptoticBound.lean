import Parameters

namespace Erdos1063
open Filter Real Asymptotics
open scoped Topology

theorem exponentCost_mul_scale {k : ℕ} (hk : 2^16 ≤ k) :
    exponentCost k * scale k ≤ 17*k := by
  have ht := scale_ge_of_pow_le hk
  have hc := (parameter_arithmetic ht (scale_pow_le k)).2.2.2
  have htk : scale k ≤ k := le_trans
    (by simpa using Nat.pow_le_pow_right (by omega : 0 < scale k) (by decide : 1 ≤ 16))
    (scale_pow_le k)
  change cost k * scale k ≤ 7*k at hc
  unfold exponentCost
  nlinarith

theorem anchor_log_bound {k : ℕ} (hk : 2^16 ≤ k)
    (hsmall : log ((scale k : ℝ)+1) ≤ (log 2 / 4096) * ((scale k : ℝ)+1)) :
    log 4 + (exponentCost k : ℝ)*log k ≤ (log 2 / 4) * k := by
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have ht := scale_ge_of_pow_le hk
  have htR : (2 : ℝ) ≤ scale k := by exact_mod_cast ht
  have hkR : (32 : ℝ) ≤ k := by exact_mod_cast (show 32 ≤ k by norm_num at hk; omega)
  have hpow : (k : ℝ) ≤ ((scale k : ℝ)+1)^16 := by
    exact_mod_cast le_of_lt (lt_scale_succ_pow k)
  have hlog := log_le_log (by positivity : (0 : ℝ) < k) hpow
  rw [log_pow] at hlog
  have hlogSmall : log (k : ℝ) ≤ 32*(log 2/4096)*(scale k : ℝ) := by
    norm_num at hlog
    nlinarith
  have hc : (exponentCost k : ℝ)*(scale k : ℝ) ≤ 17*(k : ℝ) := by
    exact_mod_cast exponentCost_mul_scale hk
  have hmul := mul_le_mul_of_nonneg_left hlogSmall (Nat.cast_nonneg (exponentCost k) : (0 : ℝ) ≤ _)
  have hcost := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 32*(log (2 : ℝ)/4096))
  have h32 := mul_le_mul_of_nonneg_left hkR (le_of_lt h2)
  have hlog4 : log (4 : ℝ) = 2*log 2 := by
    have := log_pow (2 : ℝ) 2
    norm_num at this
    linarith
  rw [hlog4]
  nlinarith

theorem eventually_anchor_log_bound : ∀ᶠ k : ℕ in atTop,
    log 4 + (exponentCost k : ℝ)*log k ≤ (log 2 / 4) * k := by
  have hδ : 0 < log (2 : ℝ)/4096 := by positivity
  have hreal := Real.isLittleO_log_id_atTop.bound hδ
  have hnat : ∀ᶠ t : ℕ in atTop, ‖log (t : ℝ)‖ ≤ (log 2/4096)*‖(t : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨N,hN⟩ := eventually_atTop.mp hnat
  filter_upwards [eventually_ge_atTop (2^16), eventually_ge_atTop (N^16)] with k hk hkN
  apply anchor_log_bound hk
  have ht : N ≤ scale k+1 := by have := scale_ge_of_pow_le hkN; omega
  have hb := hN (scale k+1) ht
  have ht2 := scale_ge_of_pow_le hk
  have hlog0 : 0 ≤ log (((scale k+1 : ℕ) : ℝ)) := log_nonneg (by exact_mod_cast (show 1 ≤ scale k+1 by omega))
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (scale k+1) : (0 : ℝ) ≤ _)] at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

theorem eventually_prime_log_bound : ∀ᶠ k : ℕ in atTop,
    (k.primeCounting : ℝ) * log ((scale k : ℝ)^2) ≤ (log 2/2)*k := by
  have hreal := Chebyshev.eventually_primeCounting_le (ε := log 4) (log_pos (by norm_num))
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (2^16)] with k hpi hk
  simp only [Nat.floor_natCast] at hpi
  have ht := scale_ge_of_pow_le hk
  have ht0 : (0 : ℝ) < scale k := by exact_mod_cast (show 0 < scale k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by norm_num at hk; omega)
  have hklog : 0 < log (k : ℝ) := log_pos hk1
  have hpBound := (le_div_iff₀ hklog).mp hpi
  have hlog := log_le_log (pow_pos ht0 16) (show (scale k : ℝ)^16 ≤ k by exact_mod_cast scale_pow_le k)
  rw [log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k.primeCounting : (0 : ℝ) ≤ _)
  have hlog4 : log (4 : ℝ) = 2*log 2 := by
    have := log_pow (2 : ℝ) 2
    norm_num at this
    linarith
  rw [hlog4] at hpBound
  rw [log_pow]
  norm_num at hmul ⊢
  nlinarith

def coarseBound (k : ℕ) : ℕ := 4*k^(exponentCost k) * ((scale k)^2)^k.primeCounting
noncomputable def improvedUpper (k : ℕ) : ℝ := exp ((3/4 : ℝ)*log 2*k)

theorem eventually_coarse_bound : ∀ᶠ k : ℕ in atTop, (coarseBound k : ℝ) ≤ improvedUpper k := by
  filter_upwards [eventually_anchor_log_bound,eventually_prime_log_bound,
    eventually_ge_atTop (2^16)] with k ha hp hk
  have ht := scale_ge_of_pow_le hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by norm_num at hk; omega)
  have ht0 : (0 : ℝ) < scale k := by exact_mod_cast (show 0 < scale k by omega)
  have hcb : (0 : ℝ) < coarseBound k := by
    unfold coarseBound
    push_cast
    positivity
  have he : log (coarseBound k : ℝ) = log 4 + (exponentCost k : ℝ)*log k +
      (k.primeCounting : ℝ)*log ((scale k : ℝ)^2) := by
    unfold coarseBound
    push_cast
    rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity), log_pow, log_pow]
  have hlog : log (coarseBound k : ℝ) ≤ (3/4 : ℝ)*log 2*k := by rw [he]; linarith
  have hexp := exp_le_exp.mpr hlog
  rwa [exp_log hcb] at hexp

#print axioms eventually_anchor_log_bound
#print axioms eventually_prime_log_bound
#print axioms eventually_coarse_bound
end Erdos1063
