/-
Copyright 2026. Released under Apache-2.0.
Actual witnesses, natural infimum, and the complete O / o endpoint.
This file contains theorem bodies; successful compilation is still a separate check.
-/
import JSP000883.FiniteConstruction
import JSP000883.PrimeInterval
import JSP000883.Growth

namespace JSP000883

open Filter Asymptotics

/-- Eventual witnesses and the claimed constant-three upper bound. -/
theorem eventualUpper : EventualUpperClaim := by
  obtain ⟨K, hK9, hK⟩ := eventualPrimeInterval
  refine ⟨K, ?_⟩
  intro k hk
  obtain ⟨p, hp, hlo, hup⟩ := hK k hk
  exact leastN_le_of_prime (hK9.trans hk) hp hlo hup

/-- The natural infimum is attained in its genuine defining set, eventually. -/
theorem eventually_leastN_admissible :
    ∀ᶠ k : ℕ in atTop, Admissible k (leastN k) := by
  obtain ⟨K, hK⟩ := eventualUpper
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  exact Nat.sInf_mem (hK k hk).1

/-- Big-O proved by a uniform constant after an actual witness is constructed. -/
theorem leastN_isBigO_lcm :
    (fun k : ℕ => (leastN k : ℝ)) =O[atTop]
      (fun k : ℕ => (lcmInitial k : ℝ)) := by
  have hO : Asymptotics.IsBigOWith 3 atTop
      (fun k : ℕ => (leastN k : ℝ)) (fun k : ℕ => (lcmInitial k : ℝ)) := by
    apply Asymptotics.IsBigOWith.of_bound
    obtain ⟨K, hK⟩ := eventualUpper
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    have hb : (leastN k : ℝ) ≤ 3 * (lcmInitial k : ℝ) := by
      exact_mod_cast (hK k hk).2
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg ((Nat.cast_nonneg (leastN k) : (0 : ℝ) ≤ (leastN k : ℝ))),
      abs_of_nonneg ((Nat.cast_nonneg (lcmInitial k) : (0 : ℝ) ≤ (lcmInitial k : ℝ)))] using hb
  exact hO.isBigO

/-- All hypotheses are discharged: the selected upper bound is `L_k`. -/
theorem betterUpper : BetterUpperClaim :=
  ⟨leastN_isBigO_lcm, lcm_isLittleO_k_mul_lcm⟩

/-- Exact inline form of the original `better_upper` target, selecting `U=L`.
The LCM is computed in naturals before being cast to reals. -/
theorem erdos_1063_better_upper :
    let n : ℕ → ℕ := fun k =>
      sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
        ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}
    let upper_bound : ℕ → ℝ := fun k =>
      (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
      upper_bound =o[atTop] (fun k =>
        (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)) := by
  exact betterUpper

end JSP000883
