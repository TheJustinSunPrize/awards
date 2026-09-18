import AsymptoticBound
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
JSP-000883 / Erdős 1063: a formal improved upper bound.
The definition of `n` and target below match the Formal Conjectures statement,
with the LCM taken in ℕ before casting to ℝ. That statement is Apache-2.0,
copyright 2026 The Formal Conjectures Authors.

This proves the `better_upper` target, not a matching lower bound or an exact
asymptotic estimate for n_k. Mathematical construction adapted from the cited
2026 prior art; see the accompanying attribution and proof outline.
-/

namespace Erdos1063
open Filter Real Asymptotics
open scoped Topology

noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2*k ≤ m ∧ ∃ i0 < k, ¬ (m-i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m-i) ∣ m.choose k}

def benchmark (k : ℕ) : ℝ :=
  (k : ℝ) * (((Finset.Icc 1 (k-1)).lcm id : ℕ) : ℝ)

theorem eventually_n_le_upper : ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ improvedUpper k := by
  filter_upwards [eventually_coarse_bound,eventually_ge_atTop (2^16)] with k hb hk
  obtain ⟨w,hw,hprop,hbound⟩ := parameter_witness hk
  have hn : n k ≤ w := Nat.sInf_le ⟨hw,hprop⟩
  have hnc : n k ≤ coarseBound k := le_trans hn hbound
  exact le_trans (by exact_mod_cast hnc) hb

theorem n_isBigO_upper : (fun k => (n k : ℝ)) =O[atTop] improvedUpper := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_n_le_upper] with k hk
  simpa [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (n k) : (0 : ℝ) ≤ _),
    abs_of_pos (exp_pos _),improvedUpper] using hk

theorem exponential_isBigO_benchmark :
    (fun k : ℕ => exp (log 2*k)) =O[atTop] benchmark := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hb := Chebyshev.two_pow_le_mul_lcmUpto (k-1)
  rw [Nat.sub_add_cancel hk] at hb
  have hb2 := Nat.mul_le_mul_left 2 hb
  have he : 2*2^(k-1) = 2^k := by
    rw [← pow_succ',Nat.sub_add_cancel hk]
  rw [he] at hb2
  have hreal : (2 : ℝ)^k ≤ 2*benchmark k := by
    unfold benchmark
    exact_mod_cast hb2
  have hexp : exp (log (2 : ℝ)*(k : ℝ)) = (2 : ℝ)^k := by
    rw [mul_comm, exp_nat_mul, exp_log (by norm_num)]
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), hexp,
    Real.norm_eq_abs, abs_of_nonneg (by unfold benchmark; positivity)]
  exact hreal

theorem upper_isLittleO_benchmark : improvedUpper =o[atTop] benchmark := by
  have he : improvedUpper =o[atTop] (fun k : ℕ => exp (log 2*k)) := by
    unfold improvedUpper
    rw [Real.isLittleO_exp_comp_exp_comp]
    have ht : Tendsto (fun k : ℕ => (log (2 : ℝ)/4)*(k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop' (by positivity)
    convert ht using 1
    funext k
    ring
  exact he.trans_isBigO exponential_isBigO_benchmark

/-- Explicit solution of the official better-upper-bound target. -/
theorem erdos_1063.better_upper :
    (fun k => (n k : ℝ)) =O[atTop] improvedUpper ∧
    improvedUpper =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k-1)).lcm id : ℕ) : ℝ) :=
  ⟨n_isBigO_upper, upper_isLittleO_benchmark⟩

#print axioms erdos_1063.better_upper
end Erdos1063
