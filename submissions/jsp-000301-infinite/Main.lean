/-
Released under the Apache 2.0 license; see the repository LICENSE.
Prepared with OpenAI Codex assistance.

The mathematics is classical: Golomb's seed (12167, 12168) and
Walker's Pell-equation multiplication method (1976, Lemma 3.3).
-/
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

namespace JSP000301

/-- Every prime divisor occurs at least twice; zero is excluded. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Multiply a solution of `2*y² - 23*x² = 1` by `24335 + 3588*√46`. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (23, 78)
  | k + 1 =>
    let (x, y) := pellPair k
    (24335 * x + 7176 * y, 82524 * x + 24335 * y)

private theorem invariants (k : ℕ) :
    let (x, y) := pellPair k
    23 * x ^ 2 + 1 = 2 * y ^ 2 ∧ 23 ∣ x ∧ 2 ∣ y ∧ k + 23 ≤ x ∧ 0 < y := by
  induction k with
  | zero => norm_num [pellPair]
  | succ k ih =>
    obtain ⟨heq, hx23, hy2, hx, hy⟩ := ih
    dsimp [pellPair] at *
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · nlinarith [heq]
    · exact dvd_add (dvd_mul_of_dvd_right hx23 _)
        (dvd_mul_of_dvd_left (by norm_num : 23 ∣ 7176) _)
    · exact dvd_add (dvd_mul_of_dvd_left (by norm_num : 2 ∣ 82524) _)
        (dvd_mul_of_dvd_right hy2 _)
    · omega
    · omega

private theorem powerful_mul_sq {c x : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hcx : c ∣ x) : Powerful (c * x ^ 2) := by
  refine ⟨Nat.mul_pos hc (pow_pos hx _), fun p hp hpn => ?_⟩
  have hpx : p ∣ x := (hp.dvd_mul.mp hpn).elim
    (fun hpc => dvd_trans hpc hcx) (fun hpx2 => hp.dvd_of_dvd_pow hpx2)
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpx 2) c

private theorem prime_mul_sq_not_square {p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) :
    ¬ IsSquare (p * x ^ 2) := by
  intro h
  have heven := Nat.isSquare_iff_even_factorization.mp h p hp
  rw [Nat.factorization_mul hp.ne_zero (pow_ne_zero _ hx), Nat.factorization_pow,
    hp.factorization] at heven
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.smul_apply,
    smul_eq_mul] at heven
  obtain ⟨a, ha⟩ := heven
  omega

/-- A concrete infinite family of counterexamples, beginning with Golomb's pair. -/
def counterexample (k : ℕ) : ℕ := 23 * (pellPair k).1 ^ 2

theorem counterexample_properties (k : ℕ) :
    Powerful (counterexample k) ∧ Powerful (counterexample k + 1) ∧
      ¬ IsSquare (counterexample k) ∧ ¬ IsSquare (counterexample k + 1) := by
  obtain ⟨heq, hx23, hy2, hx, hy⟩ := invariants k
  have hxpos : 0 < (pellPair k).1 := by omega
  have hnext : counterexample k + 1 = 2 * (pellPair k).2 ^ 2 := heq
  refine ⟨powerful_mul_sq (by norm_num) hxpos hx23, ?_,
    prime_mul_sq_not_square (by norm_num) (by omega), ?_⟩
  · rw [hnext]
    exact powerful_mul_sq (by norm_num) hy hy2
  · rw [hnext]
    exact prime_mul_sq_not_square (by norm_num) (by omega)

/-- Counterexamples exist above every bound, not merely in a checked finite range. -/
theorem unbounded_counterexamples (B : ℕ) :
    ∃ n > B, Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨counterexample B, ?_, counterexample_properties B⟩
  obtain ⟨_, _, _, hx, _⟩ := invariants B
  dsimp [counterexample]
  have hsq := Nat.le_self_pow (by decide : 2 ≠ 0) (pellPair B).1
  omega

/-- Direct negation of the precise yes/no question recorded as JSP-000301. -/
theorem jsp_000301 :
    ¬ ∀ n : ℕ, Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨n, _, hn, hn1, hnsq, hn1sq⟩ := unbounded_counterexamples 0
  exact (h n hn hn1).elim hnsq hn1sq

end JSP000301

#print axioms JSP000301.counterexample_properties
#print axioms JSP000301.unbounded_counterexamples
#print axioms JSP000301.jsp_000301
