import Mathlib

/-!
# Erdős Problem 322, the case `k = 3` (Mahler 1936)

Hardy and Littlewood's Hypothesis K fails for cubes: Mahler showed that there are infinitely many
`n` with at least `≫ n ^ (1/12)` representations as a sum of three positive cubes.

`representationCount` is copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/322.lean`, Apache-2.0).
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of positive integers. The bases can be restricted to the interval from `1` to `n`,
since `x ≤ x ^ k` for positive `x`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∀ i, 0 < (a i : ℕ)) ∧ ∑ i, (a i : ℕ) ^ k = n)).card

/-- Mahler's identity, homogenised: `(9p⁴)³ + (3pq³ - 9p⁴)³ + (q⁴ - 9p³q)³ = q¹²`. -/
theorem mahler_identity (p q : ℤ) :
    (9 * p ^ 4) ^ 3 + (3 * p * q ^ 3 - 9 * p ^ 4) ^ 3 + (q ^ 4 - 9 * p ^ 3 * q) ^ 3 = q ^ 12 := by
  ring

/-- For `1 ≤ p` and `4p ≤ q`, the three terms of Mahler's identity are positive natural
numbers. -/
theorem mahler_nat {p q : ℕ} (hp : 1 ≤ p) (hq : 4 * p ≤ q) :
    0 < 9 * p ^ 4 ∧ 9 * p ^ 4 < 3 * p * q ^ 3 ∧ 9 * p ^ 3 * q < q ^ 4 ∧
      (9 * p ^ 4) ^ 3 + (3 * p * q ^ 3 - 9 * p ^ 4) ^ 3 + (q ^ 4 - 9 * p ^ 3 * q) ^ 3
        = q ^ 12 := by
  have hcube : (4 * p) ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hp3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp
  have hq0 : 0 < q := by omega
  have h9 : 9 * p ^ 3 < q ^ 3 := by nlinarith
  have h1 : 9 * p ^ 4 < 3 * p * q ^ 3 := by nlinarith
  have h2 : 9 * p ^ 3 * q < q ^ 4 := by nlinarith
  refine ⟨by positivity, h1, h2, ?_⟩
  zify [h1.le, h2.le]
  ring

/-- Mahler: `q ^ 12` has at least `q / 4` ordered representations as a sum of three positive
cubes. -/
theorem le_representationCount_three (q : ℕ) : q / 4 ≤ representationCount 3 (q ^ 12) := by
  classical
  set n := q ^ 12 with hn
  let f : ℕ → (Fin 3 → Fin (n + 1)) := fun p =>
    ![Fin.ofNat (n + 1) (9 * p ^ 4), Fin.ofNat (n + 1) (3 * p * q ^ 3 - 9 * p ^ 4),
      Fin.ofNat (n + 1) (q ^ 4 - 9 * p ^ 3 * q)]
  -- each of `a, b, c` with `a ^ 3 + b ^ 3 + c ^ 3 = n` is at most `n`
  have hsmall : ∀ {a b c : ℕ}, a ^ 3 + b ^ 3 + c ^ 3 = n →
      a < n + 1 ∧ b < n + 1 ∧ c < n + 1 := by
    intro a b c h
    have ha : a ≤ a ^ 3 := Nat.le_self_pow (by norm_num) a
    have hb : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
    have hc : c ≤ c ^ 3 := Nat.le_self_pow (by norm_num) c
    omega
  have hIcc : (Finset.Icc 1 (q / 4)).card = q / 4 := by simp
  rw [← hIcc, representationCount]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    obtain ⟨h0, h1, h2, hsum⟩ := mahler_nat (p := p) (q := q) hp'.1 (by omega)
    obtain ⟨ha, hb, hc⟩ := hsmall hsum
    have hb0 : 0 < 3 * p * q ^ 3 - 9 * p ^ 4 := by omega
    have hc0 : 0 < q ^ 4 - 9 * p ^ 3 * q := by omega
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [f, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
          Nat.mod_eq_of_lt hc, h0, hb0, hc0]
    · have ha' : 9 * p ^ 4 < q ^ 12 + 1 := hn ▸ ha
      have hb' : 3 * p * q ^ 3 - 9 * p ^ 4 < q ^ 12 + 1 := hn ▸ hb
      have hc' : q ^ 4 - 9 * p ^ 3 * q < q ^ 12 + 1 := hn ▸ hc
      simp [f, Fin.sum_univ_three, hn, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb',
        Nat.mod_eq_of_lt hc', hsum]
  · intro p₁ hp₁ p₂ hp₂ hf
    have hp₁' := Finset.mem_Icc.mp hp₁
    have hp₂' := Finset.mem_Icc.mp hp₂
    obtain ⟨-, -, -, hsum₁⟩ := mahler_nat (p := p₁) (q := q) hp₁'.1 (by omega)
    obtain ⟨-, -, -, hsum₂⟩ := mahler_nat (p := p₂) (q := q) hp₂'.1 (by omega)
    have ha₁ := (hsmall hsum₁).1
    have ha₂ := (hsmall hsum₂).1
    have h0 := congrArg (fun g => (g 0 : ℕ)) hf
    simp only [f, Matrix.cons_val_zero, Fin.val_ofNat, Nat.mod_eq_of_lt ha₁,
      Nat.mod_eq_of_lt ha₂] at h0
    have h4 : p₁ ^ 4 = p₂ ^ 4 := by omega
    exact Nat.pow_left_injective (by norm_num) h4

theorem rpow_one_div_24 {x : ℝ} (hx : 0 ≤ x) : (x ^ 24) ^ (1 / 24 : ℝ) = x := by
  have h : (1 / 24 : ℝ) = ((24 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

/-- For `t ≥ 3`, the integer `n = (4t²)¹²` satisfies `n ^ (1/24) = 2t < t² ≤ r₃(n)`. -/
theorem mem_of_three_le {t : ℕ} (ht : 3 ≤ t) :
    ((((4 * t ^ 2) ^ 12 : ℕ) : ℝ)) ^ (1 / 24 : ℝ) < representationCount 3 ((4 * t ^ 2) ^ 12) := by
  have hcount := le_representationCount_three (4 * t ^ 2)
  rw [show 4 * t ^ 2 / 4 = t ^ 2 by omega] at hcount
  have hpow : ((((4 * t ^ 2) ^ 12 : ℕ) : ℝ)) = (2 * (t : ℝ)) ^ 24 := by push_cast; ring
  rw [hpow, rpow_one_div_24 (by positivity)]
  have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt : 2 * (t : ℝ) < (t : ℝ) ^ 2 := by nlinarith
  calc 2 * (t : ℝ) < (t : ℝ) ^ 2 := hlt
    _ = ((t ^ 2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ representationCount 3 ((4 * t ^ 2) ^ 12) := by exact_mod_cast hcount

/-- **Erdős Problem 322 for `k = 3`** (Mahler 1936): there is `c > 0` such that infinitely many
`n` have more than `n ^ c` ordered representations as a sum of three positive cubes. -/
theorem erdos_322_k_three :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite := by
  refine ⟨1 / 24, by norm_num, ?_⟩
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have hmem := hN (show (4 * (N + 3) ^ 2) ^ 12 ∈
      {n : ℕ | (n : ℝ) ^ (1 / 24 : ℝ) < representationCount 3 n} from
    mem_of_three_le (t := N + 3) (by omega))
  have h1 : N + 3 ≤ (N + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2 : 4 * (N + 3) ^ 2 ≤ (4 * (N + 3) ^ 2) ^ 12 := Nat.le_self_pow (by norm_num) _
  omega

end Erdos322
