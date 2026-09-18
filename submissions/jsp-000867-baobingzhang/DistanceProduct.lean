import Mathlib

/-!
# Erdős Problem 1045: the regular polygon does not maximise the distance product for `n = 4, 6`

Erdős, Herzog and Piranian [EHP58, p. 143] asked (https://www.erdosproblems.com/1045):

> Let `z₁, …, zₙ ∈ ℂ` with `|zᵢ - zⱼ| ≤ 2` for all `i, j`, and
> `Δ(z₁, …, zₙ) = ∏_{i ≠ j} |zᵢ - zⱼ|`.
> What is the maximum possible value of `Δ`? Is it maximised by taking the `zᵢ` to be the vertices
> of a regular polygon?

For even `n` the regular `n`-gon of diameter `2` (circumradius `1`) has `Δ = nⁿ`. Tao Hu and
Quanyu Tang (erdosproblems.com forum, October 2025; see also Cambie–Decadt–Dong–Hu–Tang,
arXiv:2603.07088) showed that the answer to the second question is *no* for `n = 4` and `n = 6`:

* `n = 4`: the kite `0, √3 + i, √3 - i, 2` has `Δ = 2¹² (2 - √3)² ≈ 294.08 > 256 = 4⁴`;
* `n = 6`: the three vertices and three arc midpoints of a Reuleaux triangle of width `2`,
  `-1, 1, √3 i, -(2 - √3) i, (√3 - 1) + i, -(√3 - 1) + i` (posted by Tang in the same thread,
  and the `n = 6` entry of Table 1 of arXiv:2603.07088), have
  `Δ = 2³³ (2 - √3)⁹ = (2√3 - 2)¹⁸ / 3⁶ · 6⁶ ≈ 1.3109 · 6⁶ > 6⁶`.

This file verifies both counterexamples. The main results are `erdos_1045_four`,
`erdos_1045_six` (an explicit configuration beating *every* regular polygon — any centre,
circumradius, rotation and labelling — satisfying the diameter constraint) and
`not_regularPolygonMaximises_four_and_six`. The general question (the value of `max Δ`, and
whether the regular polygon is optimal for odd `n`) remains open and is not addressed here.

formal-conjectures does not (as of September 2026) contain a statement of Problem 1045, so the
definitions below are written from the erdosproblems.com statement.
-/

namespace Erdos1045

open Complex Finset
open scoped Real

/-- `Δ(z₁, …, zₙ) = ∏_{i ≠ j} |zᵢ - zⱼ|`, the product over *ordered* pairs of distinct indices. -/
noncomputable def delta {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j with i ≠ j, ‖z i - z j‖

/-- The constraint of the problem: `|zᵢ - zⱼ| ≤ 2` for all `i, j`. -/
def DiamLeTwo {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∀ i j, ‖z i - z j‖ ≤ 2

/-- The vertices `c + a·e^{2πik/n}` of a regular `n`-gon with centre `c`; `‖a‖` is the
circumradius and `arg a` the rotation. -/
noncomputable def regularPolygon (n : ℕ) (c a : ℂ) (k : Fin n) : ℂ :=
  c + a * exp (2 * π * I * (k : ℕ) / n)

/-- `w` lists the vertices of a (non-degenerate) regular `n`-gon, in some order. -/
def IsRegularPolygon {n : ℕ} (w : Fin n → ℂ) : Prop :=
  ∃ (c a : ℂ) (σ : Equiv.Perm (Fin n)), a ≠ 0 ∧ ∀ k, w k = regularPolygon n c a (σ k)

/-- The question of Erdős–Herzog–Piranian for `n` points: is `Δ`, subject to all distances being
at most `2`, maximised by the vertices of a regular polygon? -/
def RegularPolygonMaximises (n : ℕ) : Prop :=
  ∃ w : Fin n → ℂ, IsRegularPolygon w ∧ DiamLeTwo w ∧
    ∀ z : Fin n → ℂ, DiamLeTwo z → delta z ≤ delta w

/-! ### General facts -/

theorem delta_nonneg {n : ℕ} (z : Fin n → ℂ) : 0 ≤ delta z :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => norm_nonneg _

theorem delta_sq {n : ℕ} (z : Fin n → ℂ) :
    delta z ^ 2 = ∏ i, ∏ j with i ≠ j, normSq (z i - z j) := by
  simp only [delta, ← prod_pow, Complex.sq_norm]

/-- `Δ` does not depend on the labelling of the points. -/
theorem delta_comp_perm {n : ℕ} (z : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    delta (z ∘ σ) = delta z := by
  simp only [delta, prod_filter, Function.comp_apply]
  rw [← Equiv.prod_comp σ (fun i => ∏ j, if i ≠ j then ‖z i - z j‖ else 1)]
  refine prod_congr rfl fun i _ => ?_
  rw [← Equiv.prod_comp σ (fun j => if σ i ≠ j then ‖z (σ i) - z j‖ else 1)]
  simp [σ.injective.ne_iff]

theorem diamLeTwo_iff {n : ℕ} (z : Fin n → ℂ) :
    DiamLeTwo z ↔ ∀ i j, normSq (z i - z j) ≤ 4 := by
  refine forall₂_congr fun i j => ?_
  rw [← Complex.sq_norm]
  constructor
  · intro h
    nlinarith [norm_nonneg (z i - z j)]
  · intro h
    nlinarith [norm_nonneg (z i - z j)]

theorem sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_lt : √3 < 1.7321 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt3_gt : 1.732 < √3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem regularPolygon_sub (n : ℕ) (c a : ℂ) (i j : Fin n) :
    regularPolygon n c a i - regularPolygon n c a j =
      a * (exp (2 * π * I / n) ^ (i : ℕ) - exp (2 * π * I / n) ^ (j : ℕ)) := by
  simp only [regularPolygon, ← exp_nat_mul]
  ring_nf

theorem isRegularPolygon_regularPolygon (n : ℕ) (c : ℂ) {a : ℂ} (ha : a ≠ 0) :
    IsRegularPolygon (regularPolygon n c a) :=
  ⟨c, a, 1, ha, fun _ => rfl⟩

/-- A relabelled regular polygon satisfying the constraint comes from one satisfying it. -/
theorem exists_of_isRegularPolygon {n : ℕ} {w : Fin n → ℂ} (hw : IsRegularPolygon w)
    (hd : DiamLeTwo w) :
    ∃ c a : ℂ, DiamLeTwo (regularPolygon n c a) ∧ delta w = delta (regularPolygon n c a) := by
  obtain ⟨c, a, σ, -, hk⟩ := hw
  have hw' : w = regularPolygon n c a ∘ σ := funext hk
  subst hw'
  exact ⟨c, a, fun i j => by simpa using hd (σ.symm i) (σ.symm j), delta_comp_perm _ _⟩

/-! ### `n = 4`: the square versus the Hu–Tang kite -/

theorem exp_two_pi_I_div_four : exp (2 * π * I / (4 : ℕ)) = I := by
  rw [show 2 * π * I / (4 : ℕ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem normSq_regularPolygon_four (c a : ℂ) (i j : Fin 4) :
    normSq (regularPolygon 4 c a i - regularPolygon 4 c a j) =
      normSq a * ![![0, 2, 4, 2], ![2, 0, 2, 4], ![4, 2, 0, 2], ![2, 4, 2, 0]] i j := by
  rw [regularPolygon_sub, exp_two_pi_I_div_four, map_mul]
  congr 1
  fin_cases i <;> fin_cases j <;> simp [normSq_apply, pow_succ] <;> norm_num

theorem delta_regularPolygon_four_sq (c a : ℂ) :
    delta (regularPolygon 4 c a) ^ 2 = normSq a ^ 12 * (4 ^ 4) ^ 2 := by
  simp only [delta_sq, normSq_regularPolygon_four, prod_filter, Fin.prod_univ_four]
  simp
  ring

/-- The square of circumradius `1` satisfies the constraint. -/
theorem diamLeTwo_square : DiamLeTwo (regularPolygon 4 0 1) := by
  rw [diamLeTwo_iff]
  intro i j
  rw [normSq_regularPolygon_four]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The square of circumradius `1` has `Δ = 4⁴`. -/
theorem delta_square : delta (regularPolygon 4 0 1) = 4 ^ 4 := by
  have h := delta_regularPolygon_four_sq 0 1
  rw [map_one, one_pow, one_mul] at h
  exact (pow_left_inj₀ (delta_nonneg _) (by norm_num) two_ne_zero).mp h

/-- Every regular `4`-gon satisfying the constraint has `Δ ≤ 4⁴`. -/
theorem delta_le_of_isRegularPolygon_four {w : Fin 4 → ℂ} (hw : IsRegularPolygon w)
    (hd : DiamLeTwo w) : delta w ≤ 4 ^ 4 := by
  obtain ⟨c, a, hd', hΔ⟩ := exists_of_isRegularPolygon hw hd
  have h02 := (diamLeTwo_iff _).mp hd' 0 2
  rw [normSq_regularPolygon_four] at h02
  simp only [Matrix.cons_val, Matrix.cons_val_zero] at h02
  have ha : normSq a ^ 12 ≤ 1 := pow_le_one₀ (normSq_nonneg a) (by linarith)
  rw [hΔ]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_
  rw [delta_regularPolygon_four_sq]
  nlinarith

/-- The kite of Hu and Tang. -/
noncomputable def kite : Fin 4 → ℂ := ![0, ⟨√3, 1⟩, ⟨√3, -1⟩, 2]

theorem normSq_kite (i j : Fin 4) : normSq (kite i - kite j) =
    ![![0, 4, 4, 4], ![4, 0, 4, 4 * (2 - √3)], ![4, 4, 0, 4 * (2 - √3)],
      ![4, 4 * (2 - √3), 4 * (2 - √3), 0]] i j := by
  have hs := sqrt3_sq
  fin_cases i <;> fin_cases j <;> simp [kite, normSq_apply] <;> linarith [hs]

theorem diamLeTwo_kite : DiamLeTwo kite := by
  rw [diamLeTwo_iff]
  intro i j
  have := sqrt3_gt
  rw [normSq_kite]
  fin_cases i <;> fin_cases j <;> simp <;> linarith

theorem delta_kite : delta kite = 2 ^ 12 * (2 - √3) ^ 2 := by
  have h : delta kite ^ 2 = (2 ^ 12 * (2 - √3) ^ 2) ^ 2 := by
    simp only [delta_sq, normSq_kite, prod_filter, Fin.prod_univ_four]
    simp
    ring
  exact (pow_left_inj₀ (delta_nonneg _) (by positivity) two_ne_zero).mp h

theorem four_pow_four_lt_delta_kite : (4 : ℝ) ^ 4 < delta kite := by
  rw [delta_kite]
  have := sqrt3_lt
  have h : (1 / 4 : ℝ) < 2 - √3 := by linarith
  have h2 : (1 / 4 : ℝ) ^ 2 < (2 - √3) ^ 2 := pow_lt_pow_left₀ h (by norm_num) two_ne_zero
  nlinarith

/-- **Erdős Problem 1045, `n = 4`** (Hu–Tang). There are four points with all mutual distances at
most `2` whose distance product `Δ` exceeds that of every regular `4`-gon obeying the same
constraint. -/
theorem erdos_1045_four :
    ∃ z : Fin 4 → ℂ, DiamLeTwo z ∧
      ∀ w : Fin 4 → ℂ, IsRegularPolygon w → DiamLeTwo w → delta w < delta z :=
  ⟨kite, diamLeTwo_kite, fun _ hw hd =>
    (delta_le_of_isRegularPolygon_four hw hd).trans_lt four_pow_four_lt_delta_kite⟩

theorem not_regularPolygonMaximises_four : ¬ RegularPolygonMaximises 4 := by
  rintro ⟨w, hw, hd, hmax⟩
  obtain ⟨z, hz, hlt⟩ := erdos_1045_four
  exact (hmax z hz).not_gt (hlt w hw hd)

/-! ### `n = 6`: the regular hexagon versus a Reuleaux triangle with arc midpoints -/

/-- `e^{iπ/3} = 1/2 + (√3/2) i`. -/
noncomputable def omega : ℂ := ⟨1 / 2, √3 / 2⟩

theorem exp_two_pi_I_div_six : exp (2 * π * I / (6 : ℕ)) = omega := by
  rw [show 2 * π * I / (6 : ℕ) = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp [omega]

theorem omega_sq : omega ^ 2 = omega - 1 := by
  have hs := sqrt3_sq
  apply Complex.ext <;> simp [omega, pow_two] <;> linarith [hs]

theorem omega_pow (k : Fin 6) :
    omega ^ (k : ℕ) = ![1, omega, omega - 1, -1, -omega, 1 - omega] k := by
  have h := omega_sq
  fin_cases k <;> simp
  · linear_combination h
  · linear_combination (omega + 1) * h
  · linear_combination omega * (omega + 1) * h
  · linear_combination (omega ^ 3 + omega ^ 2 - 1) * h

theorem normSq_regularPolygon_six (c a : ℂ) (i j : Fin 6) :
    normSq (regularPolygon 6 c a i - regularPolygon 6 c a j) =
      normSq a * ![![0, 1, 3, 4, 3, 1], ![1, 0, 1, 3, 4, 3], ![3, 1, 0, 1, 3, 4],
        ![4, 3, 1, 0, 1, 3], ![3, 4, 3, 1, 0, 1], ![1, 3, 4, 3, 1, 0]] i j := by
  rw [regularPolygon_sub, exp_two_pi_I_div_six, map_mul, omega_pow, omega_pow]
  congr 1
  have hs := sqrt3_sq
  fin_cases i <;> fin_cases j <;> simp [normSq_apply, omega] <;> linarith [hs]

theorem delta_regularPolygon_six_sq (c a : ℂ) :
    delta (regularPolygon 6 c a) ^ 2 = normSq a ^ 30 * (6 ^ 6) ^ 2 := by
  simp only [delta_sq, normSq_regularPolygon_six, prod_filter, Fin.prod_univ_six]
  simp
  ring

/-- The regular hexagon of circumradius `1` satisfies the constraint. -/
theorem diamLeTwo_hexagon : DiamLeTwo (regularPolygon 6 0 1) := by
  rw [diamLeTwo_iff]
  intro i j
  rw [normSq_regularPolygon_six]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The regular hexagon of circumradius `1` has `Δ = 6⁶`. -/
theorem delta_hexagon : delta (regularPolygon 6 0 1) = 6 ^ 6 := by
  have h := delta_regularPolygon_six_sq 0 1
  rw [map_one, one_pow, one_mul] at h
  exact (pow_left_inj₀ (delta_nonneg _) (by norm_num) two_ne_zero).mp h

/-- Every regular `6`-gon satisfying the constraint has `Δ ≤ 6⁶`. -/
theorem delta_le_of_isRegularPolygon_six {w : Fin 6 → ℂ} (hw : IsRegularPolygon w)
    (hd : DiamLeTwo w) : delta w ≤ 6 ^ 6 := by
  obtain ⟨c, a, hd', hΔ⟩ := exists_of_isRegularPolygon hw hd
  have h03 := (diamLeTwo_iff _).mp hd' 0 3
  rw [normSq_regularPolygon_six] at h03
  simp only [Matrix.cons_val, Matrix.cons_val_zero] at h03
  have ha : normSq a ^ 30 ≤ 1 := pow_le_one₀ (normSq_nonneg a) (by linarith)
  rw [hΔ]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_
  rw [delta_regularPolygon_six_sq]
  nlinarith

/-- The vertices `-1, 1, √3 i` of a Reuleaux triangle of width `2`, followed by the midpoints
`-(2 - √3) i, (√3 - 1) + i, -(√3 - 1) + i` of its three arcs. -/
noncomputable def reuleauxSix : Fin 6 → ℂ :=
  ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, √3⟩, ⟨0, -(2 - √3)⟩, ⟨√3 - 1, 1⟩, ⟨-(√3 - 1), 1⟩]

theorem normSq_reuleauxSix (i j : Fin 6) : normSq (reuleauxSix i - reuleauxSix j) =
    ![![0, 4, 4, 4 * (2 - √3), 4, 4 * (2 - √3)],
      ![4, 0, 4, 4 * (2 - √3), 4 * (2 - √3), 4],
      ![4, 4, 0, 4, 4 * (2 - √3), 4 * (2 - √3)],
      ![4 * (2 - √3), 4 * (2 - √3), 4, 0, 8 * (2 - √3), 8 * (2 - √3)],
      ![4, 4 * (2 - √3), 4 * (2 - √3), 8 * (2 - √3), 0, 8 * (2 - √3)],
      ![4 * (2 - √3), 4, 4 * (2 - √3), 8 * (2 - √3), 8 * (2 - √3), 0]] i j := by
  have hs := sqrt3_sq
  fin_cases i <;> fin_cases j <;> simp [reuleauxSix, normSq_apply] <;> linarith [hs]

theorem diamLeTwo_reuleauxSix : DiamLeTwo reuleauxSix := by
  rw [diamLeTwo_iff]
  intro i j
  have := sqrt3_gt
  rw [normSq_reuleauxSix]
  fin_cases i <;> fin_cases j <;> simp <;> linarith

theorem delta_reuleauxSix : delta reuleauxSix = 2 ^ 33 * (2 - √3) ^ 9 := by
  have ht : 0 ≤ 2 - √3 := by linarith [sqrt3_lt]
  have h : delta reuleauxSix ^ 2 = (2 ^ 33 * (2 - √3) ^ 9) ^ 2 := by
    simp only [delta_sq, normSq_reuleauxSix, prod_filter, Fin.prod_univ_six]
    simp
    ring
  exact (pow_left_inj₀ (delta_nonneg _) (by positivity) two_ne_zero).mp h

theorem six_pow_six_lt_delta_reuleauxSix : (6 : ℝ) ^ 6 < delta reuleauxSix := by
  rw [delta_reuleauxSix]
  have := sqrt3_lt
  have h : (0.2679 : ℝ) < 2 - √3 := by linarith
  have h2 : (0.2679 : ℝ) ^ 9 < (2 - √3) ^ 9 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  nlinarith

/-- **Erdős Problem 1045, `n = 6`** (Hu–Tang). There are six points with all mutual distances at
most `2` whose distance product `Δ` exceeds that of every regular `6`-gon obeying the same
constraint. -/
theorem erdos_1045_six :
    ∃ z : Fin 6 → ℂ, DiamLeTwo z ∧
      ∀ w : Fin 6 → ℂ, IsRegularPolygon w → DiamLeTwo w → delta w < delta z :=
  ⟨reuleauxSix, diamLeTwo_reuleauxSix, fun _ hw hd =>
    (delta_le_of_isRegularPolygon_six hw hd).trans_lt six_pow_six_lt_delta_reuleauxSix⟩

theorem not_regularPolygonMaximises_six : ¬ RegularPolygonMaximises 6 := by
  rintro ⟨w, hw, hd, hmax⟩
  obtain ⟨z, hz, hlt⟩ := erdos_1045_six
  exact (hmax z hz).not_gt (hlt w hw hd)

/-- **Erdős Problem 1045**: for `n = 4` and `n = 6` the answer to "is `Δ` maximised by the
vertices of a regular polygon?" is no. -/
theorem not_regularPolygonMaximises_four_and_six :
    ¬ RegularPolygonMaximises 4 ∧ ¬ RegularPolygonMaximises 6 :=
  ⟨not_regularPolygonMaximises_four, not_regularPolygonMaximises_six⟩

end Erdos1045
