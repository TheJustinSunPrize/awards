/-
Copyright 2026. Released under Apache-2.0.
The only external mathematical input is the proved Chebyshev asymptotic in
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e, itself built on
Kontorovich, Tao, and collaborators' Prime Number Theorem + project.
It is imported as a theorem, never postulated as an axiom or a hypothesis of
our final result. scripts/fetch_pnt.py fetches its pinned source dependency closure.
-/
import JSP000883.Targets
import PrimeNumberTheoremAnd.Consequences

namespace JSP000883

open Filter Asymptotics Finset

/-- A strict increase in the actual prime sum forces a prime in the interval. -/
lemma prime_between_of_theta_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hθ : Chebyshev.theta a < Chebyshev.theta b) :
    ∃ p : ℕ, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  classical
  by_contra hn
  have hb : 0 ≤ b := ha.trans hab
  have hsets :
      ((Icc 0 ⌊b⌋₊).filter Nat.Prime) = ((Icc 0 ⌊a⌋₊).filter Nat.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpb⟩, hp⟩
      have hpbr : (p : ℝ) ≤ b := (Nat.le_floor_iff hb).mp hpb
      have hpar : (p : ℝ) ≤ a := by
        by_contra hh
        exact hn ⟨p, hp, lt_of_not_ge hh, hpbr⟩
      exact ⟨⟨hp0, Nat.le_floor hpar⟩, hp⟩
    · rintro ⟨⟨hp0, hpa⟩, hp⟩
      have hpar : (p : ℝ) ≤ a := (Nat.le_floor_iff ha).mp hpa
      exact ⟨⟨hp0, Nat.le_floor (hpar.trans hab)⟩, hp⟩
  have heq : Chebyshev.theta b = Chebyshev.theta a := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, hsets]
  exact (ne_of_lt hθ) heq.symm

/-- The prime-distribution obligation is discharged from a proved PNT theorem.
We use `(k/2,3k/5]`, leaving enough slack for the integer `+2` in the target. -/
theorem eventualPrimeInterval : EventualPrimeIntervalClaim := by
  have hsmall :
      (fun x : ℝ => Chebyshev.theta x - x) =o[atTop] (fun x : ℝ => x) := by
    exact chebyshev_asymptotic
  have hclose := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 20)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hclose
  obtain ⟨K, hK⟩ := exists_nat_gt (max (20 : ℝ) (2 * X))
  have hK20r : (20 : ℝ) < K := (le_max_left _ _).trans_lt hK
  have hK20 : 20 < K := by exact_mod_cast hK20r
  refine ⟨K, by omega, ?_⟩
  intro k hk
  have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hk20 : (20 : ℝ) ≤ k := by linarith
  have hkX : 2 * X < (k : ℝ) :=
    ((le_max_right (20 : ℝ) (2 * X)).trans_lt hK).trans_le hKk
  have haX : X ≤ (k : ℝ) / 2 := by linarith
  have hbX : X ≤ 3 * (k : ℝ) / 5 := by linarith
  have ha0 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  have hb0 : (0 : ℝ) ≤ 3 * (k : ℝ) / 5 := by positivity
  have ha := hX ((k : ℝ) / 2) haX
  have hb := hX (3 * (k : ℝ) / 5) hbX
  change ‖Chebyshev.theta ((k : ℝ) / 2) - (k : ℝ) / 2‖ ≤
    (1 / 20 : ℝ) * ‖(k : ℝ) / 2‖ at ha
  change ‖Chebyshev.theta (3 * (k : ℝ) / 5) - 3 * (k : ℝ) / 5‖ ≤
    (1 / 20 : ℝ) * ‖3 * (k : ℝ) / 5‖ at hb
  simp only [Real.norm_eq_abs, abs_of_nonneg ha0] at ha
  simp only [Real.norm_eq_abs, abs_of_nonneg hb0] at hb
  obtain ⟨haL, haU⟩ := abs_le.mp ha
  obtain ⟨hbL, hbU⟩ := abs_le.mp hb
  have htheta : Chebyshev.theta ((k : ℝ) / 2) <
      Chebyshev.theta (3 * (k : ℝ) / 5) := by linarith
  obtain ⟨p, hp, hpa, hpb⟩ :=
    prime_between_of_theta_lt ha0 (by linarith) htheta
  refine ⟨p, hp, ?_, ?_⟩
  · have hh : (k : ℝ) < 2 * (p : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : 3 * (p : ℝ) + 2 ≤ 2 * (k : ℝ) := by linarith
    exact_mod_cast hh

end JSP000883
