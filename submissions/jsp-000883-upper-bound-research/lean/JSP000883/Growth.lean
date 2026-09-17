/- Copyright 2026. Released under Apache-2.0. -/
import JSP000883.Targets

namespace JSP000883
open Filter Asymptotics

/-- This little-o step needs no theorem about the growth of the LCM:
for each fixed natural `r`, eventually `r ≤ k`, hence `r*L_k ≤ k*L_k`. -/
theorem lcm_isLittleO_k_mul_lcm :
    (fun k : ℕ => (lcmInitial k : ℝ)) =o[atTop]
      (fun k : ℕ => (k : ℝ) * (lcmInitial k : ℝ)) := by
  apply Asymptotics.isLittleO_iff_nat_mul_le.mpr
  intro r
  filter_upwards [Filter.eventually_ge_atTop r] with k hk
  have hL : (0 : ℝ) ≤ (lcmInitial k : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ (k : ℝ) * (lcmInitial k : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) hL
  change (r : ℝ) * ‖(lcmInitial k : ℝ)‖ ≤
    ‖(k : ℝ) * (lcmInitial k : ℝ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg hL, Real.norm_eq_abs, abs_of_nonneg hprod]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hL


end JSP000883
