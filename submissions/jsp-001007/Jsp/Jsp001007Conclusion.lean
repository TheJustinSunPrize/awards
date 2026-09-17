/-
Copyright 2026. Released under Apache-2.0; see LICENSE.
-/
import Jsp.Jsp001007Final

namespace JSP001007

/-- The final counterexample refutes the recorded conjecture at ε = 1/10. -/
theorem not_green44_conjecture : ¬JSP001007.Green44Conjecture (1 / 10 : ℝ) := by
  rintro ⟨k, hk⟩
  by_cases hz : k = 0
  · subst k
    let p : Fin 0 → ℕ := Fin.elim0
    let A : (i : Fin 0) → Finset (ZMod (p i)) := fun i => Fin.elim0 i
    have hc : JSP001007.AdmissibleConfig (1 / 10 : ℝ) 1 0 p A :=
      ⟨fun i => Fin.elim0 i, fun i _ _ => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    have hbad := hk 1 p A hc
    norm_num [JSP001007.survivors] at hbad
  · have hpos : 0 < k := Nat.pos_of_ne_zero hz
    let : NeZero k := ⟨hz⟩
    obtain ⟨N₀, hN₀⟩ := JSP001007.green44_counterexample k hpos
    obtain ⟨p, A, hprime, hmono, hpowers, hcards, hsurv⟩ := hN₀ N₀ le_rfl
    have hc : JSP001007.AdmissibleConfig (1 / 10 : ℝ) N₀ k p A := by
      refine ⟨hprime, hmono, hcards, ?_⟩
      intro i
      have hpow : (p i : ℝ) ^ 10 < ((N₀ : ℝ) ^ (9 / 10 : ℝ)) ^ 10 := by
        rw [JSP001007.rpow_nine_tenth_pow_ten]
        exact_mod_cast hpowers i
      have hlt := lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg (Nat.cast_nonneg N₀) _) hpow
      simpa only [show (1 - (1 / 10 : ℝ)) = 9 / 10 by norm_num] using hlt
    have hnat : N₀ < (JSP001007.survivors N₀ p A).card * 10 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).mp hsurv
    have hreal : (N₀ : ℝ) < ((JSP001007.survivors N₀ p A).card : ℝ) * 10 := by
      exact_mod_cast hnat
    have hbad := hk N₀ p A hc
    linarith


end JSP001007
