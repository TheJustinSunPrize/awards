import JSP000689.Colorable
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas

namespace JSP000689
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Not two-colourable in the ordinary weak hypergraph colouring sense. -/
def NotTwoColorable (H : Finset (Finset V)) : Prop :=
  ¬ ∃ c : V → Bool, ∀ e ∈ H, ¬ Mono e c

theorem exists_degree_gt (H : Finset (Finset V)) (r : ℕ) (hr : 2 ≤ r)
    (hu : ∀ e ∈ H, e.card = r) (hn : NotTwoColorable H)
    (β : ℚ) (hβ : 1 ≤ β) :
    ∃ v, (2 - β) * β ^ (r - 2) < (degree H v : ℚ) := by
  classical
  by_contra h
  push Not at h
  exact hn (colorable H r hr hu β hβ h)

/-- The exponential constant is explicit; no asymptotic notation is needed. -/
theorem exponential_comparison (r : ℕ) (hr : 6 ≤ r) :
    (9 / 8 : ℚ) ^ r ≤ (1 / 2 : ℚ) * (3 / 2 : ℚ) ^ (r - 2) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have he : r + 1 - 2 = (r - 2) + 1 := by omega
    rw [pow_succ, he, pow_succ]
    have hp : 0 ≤ (3 / 2 : ℚ) ^ (r - 2) := pow_nonneg (by norm_num) _
    nlinarith

/-- Full affirmative answer to Erdős #833, with c = 1/8, over rational numbers. -/
theorem erdos833_rat (H : Finset (Finset V)) (r : ℕ) (hr : 2 ≤ r)
    (hu : ∀ e ∈ H, e.card = r) (hn : NotTwoColorable H) :
    ∃ v, (9 / 8 : ℚ) ^ r ≤ (degree H v : ℚ) := by
  by_cases hlarge : 6 ≤ r
  · obtain ⟨v, hv⟩ := exists_degree_gt H r hr hu hn (3/2) (by norm_num)
    refine ⟨v, (exponential_comparison r hlarge).trans ?_⟩
    norm_num at hv
    linarith
  · obtain ⟨v, hv⟩ := exists_degree_gt H r hr hu hn 1 (by norm_num)
    norm_num at hv
    have hvn : 2 ≤ degree H v := by exact_mod_cast hv
    have hvq : (2 : ℚ) ≤ degree H v := by exact_mod_cast hvn
    have hr5 : r ≤ 5 := by omega
    have hp : (9 / 8 : ℚ) ^ r ≤ (9 / 8 : ℚ) ^ 5 :=
      pow_le_pow_right₀ (by norm_num) hr5
    refine ⟨v, hp.trans ?_⟩
    norm_num
    linarith

/-- The real-valued statement in the original problem: c = 1/8 works for every r ≥ 2. -/
theorem erdos833 (H : Finset (Finset V)) (r : ℕ) (hr : 2 ≤ r)
    (hu : ∀ e ∈ H, e.card = r) (hn : NotTwoColorable H) :
    ∃ v, (1 + 1 / 8 : ℝ) ^ r ≤ (degree H v : ℝ) := by
  obtain ⟨v, hv⟩ := erdos833_rat H r hr hu hn
  refine ⟨v, ?_⟩
  have hc : (1 + 1 / 8 : ℝ) = 9 / 8 := by norm_num
  rw [hc]
  have hcast := (Rat.cast_le (K := ℝ)).mpr hv
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hcast

/-- A single positive constant works uniformly over all finite sizes and ranks. -/
theorem prize_statement :
    ∃ c : ℝ, 0 < c ∧ ∀ (n r : ℕ) (H : Finset (Finset (Fin n))),
      2 ≤ r → (∀ e ∈ H, e.card = r) → NotTwoColorable H →
      ∃ v, (1 + c) ^ r ≤ (degree H v : ℝ) := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro n r H hr hu hn
  exact erdos833 H r hr hu hn

end JSP000689
