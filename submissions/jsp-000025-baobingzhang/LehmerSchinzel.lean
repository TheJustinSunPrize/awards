import Mathlib

/-!
# Lehmer's Mahler measure problem for real-rooted polynomials (Schinzel's theorem)

For `f = a (X - α₁) ⋯ (X - α_d) ∈ ℂ[X]` the Mahler measure is `M(f) = |a| ∏ max(1, |αᵢ|)`.
Lehmer's problem (1933, open) asks whether there is `μ > 1` such that every `f ∈ ℤ[X]` with
`M(f) > 1` satisfies `M(f) ≥ μ`.

This file proves the case of polynomials all of whose complex roots are real, via the theorem of
Schinzel:

* A. Schinzel, *On the product of the conjugates outside the unit circle of an algebraic number*,
  Acta Arith. 24 (1973), 385–399; Addendum, Acta Arith. 26 (1974/75), 329–331.
* G. Höhn, N.-P. Skoruppa, *Un résultat de Schinzel*, J. Théor. Nombres Bordeaux 5 (1993), 185
  (one-page proof).
* C. Smyth, *The Mahler measure of algebraic numbers: a survey* (2008), §6.1, eq. (22):
  if `α ≠ 0, ±1` is a totally real algebraic integer of degree `d`, then `M(α) ≥ φ^(d/2)`,
  where `φ = (1 + √5)/2`.

The definitions `mahlerMeasure` and `mahlerMeasureZ` are copied verbatim from Google DeepMind's
formal-conjectures project, `FormalConjectures/Wikipedia/LehmerMahlerMeasureProblem.lean`
(Apache-2.0). They are shown to agree with Mathlib's `Polynomial.mahlerMeasure`
(`mahlerMeasure_eq_polynomial_mahlerMeasure`).

## Main statements

* `schinzel_real_rooted`: if `f ∈ ℤ[X]` has only real roots and `f(0) f(1) f(-1) ≠ 0`, then
  `M(f) ≥ φ ^ (deg f / 2)` (leading coefficient arbitrary). `schinzel_real_rooted'` is the same
  statement for Mathlib's `Polynomial.mahlerMeasure`.
* `schinzel_totally_real`: the classical form, for a totally real algebraic integer
  `α ∉ {0, 1, -1}` and its minimal polynomial.
* `schinzel_real_rooted_sharp`: `(X² - X - 1)^k` satisfies all hypotheses and attains equality,
  for every `k`.
* `lehmer_mahler_measure_problem.variants.real_rooted`: if `f ∈ ℤ[X]` has only real roots and
  `M(f) > 1`, then `M(f) ≥ M(X² - X - 1) = φ` (`mahlerMeasureZ_X_sq_sub_X_sub_one`).
* `lehmer_mahler_measure_problem.variants.real_rooted_exists`: the statement of Lehmer's problem
  restricted to real-rooted `f ∈ ℤ[X]`, with `μ = φ`, which is optimal.

## Proof

Put `e = φ / (2(φ+2)) = 1/(2√5)` and `c = 1/(φ+2) = 1/2 - e`. For real `x ∉ {0, ±1}`,
`max(1, |x|) ≥ φ^(1/2) |x|^c |x² - 1|^e`, which is `φ^(1/2) |x|^(1/2) |x - 1/x|^(1/(2√5))`, the
function used by Höhn and Skoruppa. With `s = x²` (if `|x| < 1`) or `s = 1/x²` (if `|x| > 1`),
both cases reduce to `(φ+2) log φ + log s + φ log(1-s) ≤ 0` on `(0, 1)`. That follows from
`log y ≤ y - 1` at `y = s φ²` and `y = (1-s) φ`, using `φ² = φ + 1` (`core`, `pointwise`).
Summing the logarithmic form over the roots of `f = a ∏ (X - αᵢ)` (`multiset_bound`) and using
`|f(0)| = |a| ∏ |αᵢ| ≥ 1` and `|f(±1)| = |a| ∏ |αᵢ ∓ 1| ≥ 1` (nonzero integers) gives
`log M(f) ≥ (d/2) log φ + c log |a| ≥ (d/2) log φ`.

For the corollary, factors `X`, `X - 1` and `X + 1` are split off without changing `M`
(`exists_reduced`). The reduced polynomial `g` has `M(g) ≥ φ^(deg g/2) ≥ φ` if `deg g ≥ 2`. If
`deg g = 1`, then `M(g) = max(|a|, |b|) ≥ 2` for `g = aX + b` with `b, a + b, b - a ≠ 0`. If
`deg g = 0`, then `M(g) = |a|` is an integer `> 1`.
-/

namespace LehmerMahlerMeasureProblem

open Polynomial LehmerMahlerMeasureProblem

/--
The Mahler measure of `f(X)` is defined as `‖a‖ ∏ᵢ max(1,‖αᵢ‖)`,
where `f(X)=a(X-α₁)(X-α₂)...(X-αₙ)`.
-/
noncomputable def mahlerMeasure (f : ℂ[X]) : ℝ :=
  ‖f.leadingCoeff‖ * (f.roots.map (max 1 ‖·‖)).prod

noncomputable def mahlerMeasureZ (f : ℤ[X]) : ℝ :=
  mahlerMeasure (f.map (algebraMap ℤ ℂ))

end LehmerMahlerMeasureProblem

namespace LehmerSchinzel

open Real

/-- Scaled weighted AM-GM step: `(φ+2) log φ + log s + φ log (1-s) ≤ 0` on `(0,1)`. -/
lemma core (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (goldenRatio + 2) * log goldenRatio + log s + goldenRatio * log (1 - s) ≤ 0 := by
  have hφ := goldenRatio_pos
  have hsq := goldenRatio_sq
  have h1 : log (s * goldenRatio ^ 2) ≤ s * goldenRatio ^ 2 - 1 :=
    log_le_sub_one_of_pos (by positivity)
  have h2 : log ((1 - s) * goldenRatio) ≤ (1 - s) * goldenRatio - 1 :=
    log_le_sub_one_of_pos (mul_pos (by linarith) hφ)
  rw [log_mul hs0.ne' (by positivity), log_pow] at h1
  rw [log_mul (by linarith) hφ.ne'] at h2
  have h2' := mul_le_mul_of_nonneg_left h2 hφ.le
  push_cast at h1
  nlinarith

/-- Pointwise inequality (scaled by `2(φ+2)`): for real `x ∉ {0, 1, -1}`,
`(φ+2) log φ + 2 log |x| + φ (log |1-x| + log |-1-x|) ≤ 2 (φ+2) log (max 1 |x|)`. -/
lemma pointwise (x : ℝ) (h0 : x ≠ 0) (h1 : x ≠ 1) (hm1 : x ≠ -1) :
    (goldenRatio + 2) * log goldenRatio + 2 * log |x|
      + goldenRatio * (log |1 - x| + log |-1 - x|)
      ≤ 2 * (goldenRatio + 2) * log (max 1 |x|) := by
  have hφ := goldenRatio_pos
  have ha : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hb : -1 - x ≠ 0 := by intro h; apply hm1; linarith
  have hprod : log |1 - x| + log |-1 - x| = log |x ^ 2 - 1| := by
    rw [log_abs, log_abs, log_abs, ← log_mul ha hb]
    congr 1; ring
  have hx2 : log (x ^ 2) = 2 * log |x| := by
    rw [log_pow, log_abs]; push_cast; ring
  have hx2pos : 0 < x ^ 2 := by positivity
  rw [hprod]
  rcases lt_or_gt_of_ne (show |x| ≠ 1 by
      intro h; rcases abs_eq (zero_le_one) |>.mp h with h | h <;> contradiction) with hlt | hgt
  · -- |x| < 1
    have hs1 : x ^ 2 < 1 := by
      have := abs_lt.mp hlt; nlinarith
    have hmax : max 1 |x| = 1 := max_eq_left hlt.le
    have habs : |x ^ 2 - 1| = 1 - x ^ 2 := by
      rw [abs_of_neg (by linarith)]; ring
    have := core (x ^ 2) hx2pos hs1
    rw [hmax, log_one, habs]
    rw [hx2] at this
    linarith
  · -- |x| > 1
    have hs1 : 1 < x ^ 2 := by
      have : 1 < |x| ^ 2 := by nlinarith
      rwa [sq_abs] at this
    have hmax : max 1 |x| = |x| := max_eq_right hgt.le
    have habs : |x ^ 2 - 1| = x ^ 2 - 1 := abs_of_pos (by linarith)
    have hu0 : 0 < (x ^ 2)⁻¹ := inv_pos.mpr hx2pos
    have hu1 : (x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs1
    have := core ((x ^ 2)⁻¹) hu0 hu1
    have hsub : 1 - (x ^ 2)⁻¹ = (x ^ 2 - 1) / x ^ 2 := by
      field_simp
    rw [hsub, log_div (by linarith) hx2pos.ne', log_inv, hx2] at this
    rw [hmax, habs]
    nlinarith

/-- Pointwise inequality for a complex number on the real axis. -/
lemma pointwise_complex (z : ℂ) (hz : z.im = 0) (h0 : z ≠ 0) (h1 : z ≠ 1) (hm1 : z ≠ -1) :
    (goldenRatio + 2) * log goldenRatio + 2 * log ‖0 - z‖
      + goldenRatio * (log ‖1 - z‖ + log ‖-1 - z‖)
      ≤ 2 * (goldenRatio + 2) * log (max 1 ‖z‖) := by
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  rw [hz'] at h0 h1 hm1 ⊢
  have e0 : ‖(0 : ℂ) - (z.re : ℂ)‖ = |z.re| := by
    rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have e1 : ‖(1 : ℂ) - (z.re : ℂ)‖ = |1 - z.re| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have em1 : ‖(-1 : ℂ) - (z.re : ℂ)‖ = |-1 - z.re| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  rw [e0, e1, em1, Complex.norm_real, Real.norm_eq_abs]
  exact pointwise z.re (by exact_mod_cast h0) (by exact_mod_cast h1) (by exact_mod_cast hm1)

/-- The pointwise inequality summed over a multiset of real, non-`{0, ±1}` complex numbers. -/
lemma multiset_bound (R : Multiset ℂ)
    (hR : ∀ z ∈ R, z.im = 0 ∧ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1) :
    (Multiset.card R : ℝ) * ((goldenRatio + 2) * log goldenRatio)
      + 2 * log ‖(R.map (fun z => 0 - z)).prod‖
      + goldenRatio * (log ‖(R.map (fun z => 1 - z)).prod‖
        + log ‖(R.map (fun z => -1 - z)).prod‖)
      ≤ 2 * (goldenRatio + 2) * log (R.map (fun z => max 1 ‖z‖)).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    have hR' : ∀ z ∈ R, z.im = 0 ∧ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1 :=
      fun z hz => hR z (Multiset.mem_cons_of_mem hz)
    obtain ⟨ha, ha0, ha1, ham1⟩ := hR a (Multiset.mem_cons_self a R)
    have ih := ih hR'
    have hpa := pointwise_complex a ha ha0 ha1 ham1
    have n0 : ∀ w : ℂ, (∀ z ∈ R, z ≠ w) → ‖(R.map (fun z => w - z)).prod‖ ≠ 0 := by
      intro w hw
      rw [norm_ne_zero_iff]
      refine Multiset.prod_ne_zero ?_
      simp only [Multiset.mem_map, not_exists, not_and]
      intro z hz h
      exact hw z hz (sub_eq_zero.mp h).symm
    have p0 := n0 0 (fun z hz => (hR' z hz).2.1)
    have p1 := n0 1 (fun z hz => (hR' z hz).2.2.1)
    have pm1 := n0 (-1) (fun z hz => (hR' z hz).2.2.2)
    have pmax : (R.map (fun z => max 1 ‖z‖)).prod ≠ 0 := by
      refine Multiset.prod_ne_zero ?_
      simp only [Multiset.mem_map, not_exists, not_and]
      intro z _ h
      have := le_max_left 1 ‖z‖
      linarith
    have q0 : ‖(0 : ℂ) - a‖ ≠ 0 := by simpa using ha0
    have q1 : ‖(1 : ℂ) - a‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr (Ne.symm ha1)
    have qm1 : ‖(-1 : ℂ) - a‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr (Ne.symm ham1)
    have qmax : max 1 ‖a‖ ≠ 0 := by
      have := le_max_left 1 ‖a‖
      intro h; linarith
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
    rw [log_mul q0 p0, log_mul q1 p1, log_mul qm1 pm1, log_mul qmax pmax]
    push_cast
    linarith

end LehmerSchinzel

namespace LehmerMahlerMeasureProblem

open Polynomial Real LehmerSchinzel

/-- **Schinzel's theorem** (polynomial form). If `f ∈ ℤ[X]` has only real complex roots and
`f(0) f(1) f(-1) ≠ 0`, then `M(f) ≥ ((1 + √5)/2) ^ (deg f / 2)`. -/
theorem schinzel_real_rooted (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : f.eval 0 ≠ 0) (h1 : f.eval 1 ≠ 0) (hm1 : f.eval (-1) ≠ 0) :
    ((1 + √5) / 2) ^ ((f.natDegree : ℝ) / 2) ≤ mahlerMeasureZ f := by
  set g := f.map (algebraMap ℤ ℂ) with hg
  set R := g.roots with hR
  have hinj : Function.Injective (algebraMap ℤ ℂ) := RingHom.injective_int _
  have hf : f ≠ 0 := by rintro rfl; simp at h0
  have hlc : g.leadingCoeff = (f.leadingCoeff : ℂ) := leadingCoeff_map_of_injective hinj f
  have hdeg : g.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hcard : (Multiset.card R : ℝ) = f.natDegree := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hsplit : g = C g.leadingCoeff * (R.map (fun z => X - C z)).prod :=
    (IsAlgClosed.splits g).eq_prod_roots
  have heval : ∀ w : ℂ, g.eval w = g.leadingCoeff * (R.map (fun z => w - z)).prod := by
    intro w
    conv_lhs => rw [hsplit]
    simp [eval_multiset_prod, Multiset.map_map]
  have hevalint : ∀ i : ℤ, g.eval (i : ℂ) = ((f.eval i : ℤ) : ℂ) := by
    intro i; rw [hg, eval_intCast_map]; rfl
  have ha : (1 : ℝ) ≤ ‖(f.leadingCoeff : ℂ)‖ := by
    rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hf)
  have hint : ∀ i : ℤ, f.eval i ≠ 0 →
      log ‖(f.leadingCoeff : ℂ)‖ + log ‖(R.map (fun z => (i : ℂ) - z)).prod‖ ≥ 0 := by
    intro i hi
    have e := heval (i : ℂ)
    rw [hevalint, hlc] at e
    have hn : (1 : ℝ) ≤ ‖((f.eval i : ℤ) : ℂ)‖ := by
      rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hi
    rw [e, norm_mul] at hn
    have hpos : 0 < ‖(R.map (fun z => (i : ℂ) - z)).prod‖ := by
      by_contra hc
      rw [not_lt] at hc
      have : ‖(R.map (fun z => (i : ℂ) - z)).prod‖ = 0 := le_antisymm hc (norm_nonneg _)
      rw [this, mul_zero] at hn; linarith
    rw [← log_mul (by linarith) hpos.ne']
    exact log_nonneg hn
  have hR0 : ∀ z ∈ R, z.im = 0 ∧ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1 := by
    intro z hz
    have hroot : g.eval z = 0 := (mem_roots'.mp hz).2
    refine ⟨hreal z hz, ?_, ?_, ?_⟩
    · rintro rfl
      have := hevalint 0
      simp only [Int.cast_zero] at this
      rw [this] at hroot; exact h0 (by exact_mod_cast hroot)
    · rintro rfl
      have := hevalint 1
      simp only [Int.cast_one] at this
      rw [this] at hroot; exact h1 (by exact_mod_cast hroot)
    · rintro rfl
      have := hevalint (-1)
      simp only [Int.cast_neg, Int.cast_one] at this
      rw [this] at hroot; exact hm1 (by exact_mod_cast hroot)
  have hbound := multiset_bound R hR0
  have i0 := hint 0 h0
  have i1 := hint 1 h1
  have im1 := hint (-1) hm1
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg] at i0 i1 im1
  have hla : 0 ≤ log ‖(f.leadingCoeff : ℂ)‖ := log_nonneg ha
  have hφ := goldenRatio_pos
  have hφ1 := one_lt_goldenRatio
  have hlogφ : 0 < log goldenRatio := log_pos hφ1
  -- `M = ‖a‖ * P`, with `P` the product of `max 1 ‖z‖` over the roots.
  have hP : 0 < (R.map (fun z => max 1 ‖z‖)).prod := by
    refine Multiset.prod_pos ?_
    intro x hx
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : mahlerMeasureZ f = ‖(f.leadingCoeff : ℂ)‖ * (R.map (fun z => max 1 ‖z‖)).prod := by
    rw [mahlerMeasureZ, mahlerMeasure, ← hlc]
  have hMpos : 0 < mahlerMeasureZ f := by rw [hM]; exact mul_pos (by linarith) hP
  have hlogM : log (mahlerMeasureZ f) =
      log ‖(f.leadingCoeff : ℂ)‖ + log (R.map (fun z => max 1 ‖z‖)).prod := by
    rw [hM, log_mul (by linarith) hP.ne']
  -- The key linear inequality between logarithms.
  have key : (f.natDegree : ℝ) / 2 * log goldenRatio ≤ log (mahlerMeasureZ f) := by
    rw [hlogM]
    rw [hcard] at hbound
    have h2 : 0 < 2 * (goldenRatio + 2) := by positivity
    have : 2 * (goldenRatio + 2) * ((f.natDegree : ℝ) / 2 * log goldenRatio)
        ≤ 2 * (goldenRatio + 2) *
          (log ‖(f.leadingCoeff : ℂ)‖ + log (R.map (fun z => max 1 ‖z‖)).prod) := by
      nlinarith
    exact le_of_mul_le_mul_left this h2
  have hgold : (1 + √5) / 2 = goldenRatio := rfl
  rw [hgold, rpow_def_of_pos hφ, ← exp_log hMpos]
  exact exp_le_exp.mpr (by linarith)

/-- The root-product definition agrees with Mathlib's `Polynomial.mahlerMeasure`
(the exponential of the circle average of `log ‖f‖`), by Jensen's formula. -/
theorem mahlerMeasure_eq_polynomial_mahlerMeasure (p : ℂ[X]) :
    LehmerMahlerMeasureProblem.mahlerMeasure p = Polynomial.mahlerMeasure p := by
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]; rfl

theorem mahlerMeasureZ_eq (f : ℤ[X]) :
    mahlerMeasureZ f = Polynomial.mahlerMeasure (f.map (algebraMap ℤ ℂ)) :=
  mahlerMeasure_eq_polynomial_mahlerMeasure _

/-- Schinzel's theorem stated with Mathlib's `Polynomial.mahlerMeasure`. -/
theorem schinzel_real_rooted' (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : f.eval 0 ≠ 0) (h1 : f.eval 1 ≠ 0) (hm1 : f.eval (-1) ≠ 0) :
    ((1 + √5) / 2) ^ ((f.natDegree : ℝ) / 2) ≤ (f.map (algebraMap ℤ ℂ)).mahlerMeasure := by
  rw [← mahlerMeasureZ_eq]; exact schinzel_real_rooted f hreal h0 h1 hm1

/-- **Schinzel's theorem** (classical form, Smyth's survey eq. (22)). If `α ≠ 0, ±1` is a totally
real algebraic integer (all complex roots of its minimal polynomial are real), then
`M(α) ≥ ((1 + √5)/2) ^ (d/2)`, where `d` is the degree of `α` and `M(α)` is the Mahler measure of
its minimal polynomial. -/
theorem schinzel_totally_real (α : ℂ) (hα : IsIntegral ℤ α)
    (htr : ∀ z ∈ ((minpoly ℤ α).map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : α ≠ 0) (h1 : α ≠ 1) (hm1 : α ≠ -1) :
    ((1 + √5) / 2) ^ (((minpoly ℤ α).natDegree : ℝ) / 2) ≤ mahlerMeasureZ (minpoly ℤ α) := by
  have key : ∀ r : ℤ, α ≠ r → (minpoly ℤ α).eval r ≠ 0 := by
    intro r hr hroot
    have hdvd : X - C r ∣ minpoly ℤ α := dvd_iff_isRoot.mpr hroot
    obtain ⟨q, hq⟩ := (irreducible_X_sub_C r).dvd_symm (minpoly.irreducible hα) hdvd
    have : aeval α (X - C r) = 0 := by
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    apply hr
    simpa [sub_eq_zero] using this
  exact schinzel_real_rooted _ htr (key 0 (by simpa using h0)) (key 1 (by simpa using h1))
    (key (-1) (by simpa using hm1))

/-- Removing all roots `0, 1, -1` from a nonzero real-rooted integer polynomial does not change
its Mahler measure. -/
lemma exists_reduced : ∀ n : ℕ, ∀ f : ℤ[X], f.natDegree = n → f ≠ 0 →
    (∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0) →
    ∃ g : ℤ[X], g ≠ 0 ∧ (∀ z ∈ (g.map (algebraMap ℤ ℂ)).roots, z.im = 0) ∧
      g.eval 0 ≠ 0 ∧ g.eval 1 ≠ 0 ∧ g.eval (-1) ≠ 0 ∧ mahlerMeasureZ g = mahlerMeasureZ f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf hreal
  have hinj : Function.Injective (algebraMap ℤ ℂ) := RingHom.injective_int _
  have peel : ∀ r : ℤ, |r| ≤ 1 → f.eval r = 0 →
      ∃ g : ℤ[X], g ≠ 0 ∧ (∀ z ∈ (g.map (algebraMap ℤ ℂ)).roots, z.im = 0) ∧
        g.eval 0 ≠ 0 ∧ g.eval 1 ≠ 0 ∧ g.eval (-1) ≠ 0 ∧ mahlerMeasureZ g = mahlerMeasureZ f := by
    intro r hr hroot
    set q := f /ₘ (X - C r) with hq_def
    have hfq : (X - C r) * q = f := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hq : q ≠ 0 := by
      intro hq; rw [hq, mul_zero] at hfq; exact hf hfq.symm
    have hdeg : q.natDegree < n := by
      rw [← hn, ← hfq, natDegree_mul (X_sub_C_ne_zero r) hq, natDegree_X_sub_C]; omega
    have hmap : f.map (algebraMap ℤ ℂ) = (X - C (r : ℂ)) * q.map (algebraMap ℤ ℂ) := by
      rw [← hfq, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]; rfl
    have hqreal : ∀ z ∈ (q.map (algebraMap ℤ ℂ)).roots, z.im = 0 := by
      intro z hz
      apply hreal
      have hne : (X - C (r : ℂ)) * q.map (algebraMap ℤ ℂ) ≠ 0 := by
        rw [← hmap]; exact (Polynomial.map_ne_zero_iff hinj).mpr hf
      rw [hmap, roots_mul hne]
      exact Multiset.mem_add.mpr (Or.inr hz)
    obtain ⟨g, hg0, hg1, hg2, hg3, hg4, hg5⟩ := ih _ hdeg q rfl hq hqreal
    refine ⟨g, hg0, hg1, hg2, hg3, hg4, ?_⟩
    have hr' : max 1 ‖(r : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]; exact max_eq_left (by exact_mod_cast hr)
    rw [hg5, mahlerMeasureZ_eq, mahlerMeasureZ_eq, hmap, mahlerMeasure_mul,
      mahlerMeasure_X_sub_C, hr', one_mul]
  by_cases e0 : f.eval 0 = 0
  · exact peel 0 (by norm_num) (by simpa using e0)
  by_cases e1 : f.eval 1 = 0
  · exact peel 1 (by norm_num) (by simpa using e1)
  by_cases em1 : f.eval (-1) = 0
  · exact peel (-1) (by norm_num) (by simpa using em1)
  exact ⟨f, hf, hreal, e0, e1, em1, rfl⟩

/-- Over `ℂ`, `X² - X - 1 = (X - φ)(X - ψ)` with `φ = (1 + √5)/2` and `ψ = (1 - √5)/2`. -/
lemma map_X_sq_sub_X_sub_one :
    (X ^ 2 - X - 1 : ℤ[X]).map (algebraMap ℤ ℂ)
      = (X - C (goldenRatio : ℂ)) * (X - C (goldenConj : ℂ)) := by
  have hs : (goldenRatio : ℂ) + goldenConj = 1 := by exact_mod_cast goldenRatio_add_goldenConj
  have hp : (goldenRatio : ℂ) * goldenConj = -1 := by exact_mod_cast goldenRatio_mul_goldenConj
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
  have : (X - C (goldenRatio : ℂ)) * (X - C (goldenConj : ℂ))
      = X ^ 2 - C ((goldenRatio : ℂ) + goldenConj) * X + C ((goldenRatio : ℂ) * goldenConj) := by
    simp only [C_add, C_mul]; ring
  rw [this, hs, hp, C_1, C_neg, C_1]; ring

/-- The Mahler measure of `X² - X - 1` is the golden ratio. -/
theorem mahlerMeasureZ_X_sq_sub_X_sub_one :
    mahlerMeasureZ (X ^ 2 - X - 1) = (1 + √5) / 2 := by
  have hψ : |goldenConj| ≤ 1 := by
    rw [abs_of_neg goldenConj_neg]; linarith [neg_one_lt_goldenConj]
  rw [mahlerMeasureZ_eq, map_X_sq_sub_X_sub_one, mahlerMeasure_mul, mahlerMeasure_X_sub_C,
    mahlerMeasure_X_sub_C, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos goldenRatio_pos, max_eq_right one_lt_goldenRatio.le,
    max_eq_left hψ, mul_one]

/-- **Sharpness and non-vacuity.** For every `k`, `f = (X² - X - 1)^k` has only real roots,
satisfies `f(0) f(1) f(-1) ≠ 0`, has degree `2k`, and `M(f) = ((1 + √5)/2) ^ (deg f / 2)`. -/
theorem schinzel_real_rooted_sharp (k : ℕ) :
    (∀ z ∈ (((X ^ 2 - X - 1 : ℤ[X]) ^ k).map (algebraMap ℤ ℂ)).roots, z.im = 0) ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval 0 ≠ 0 ∧ ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval 1 ≠ 0 ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval (-1) ≠ 0 ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).natDegree = 2 * k ∧
      mahlerMeasureZ ((X ^ 2 - X - 1) ^ k)
        = ((1 + √5) / 2) ^ ((((X ^ 2 - X - 1 : ℤ[X]) ^ k).natDegree : ℝ) / 2) := by
  have hdeg2 : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2 := by compute_degree!
  have hdeg : ((X ^ 2 - X - 1 : ℤ[X]) ^ k).natDegree = 2 * k := by
    rw [natDegree_pow, hdeg2, mul_comm]
  refine ⟨?_, by simp, by simp, by simp, hdeg, ?_⟩
  · intro z hz
    have hne : (X - C (goldenRatio : ℂ)) * (X - C (goldenConj : ℂ)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    rw [Polynomial.map_pow, map_X_sq_sub_X_sub_one, roots_pow, roots_mul hne, roots_X_sub_C,
      roots_X_sub_C] at hz
    rcases Multiset.mem_add.mp (Multiset.mem_of_mem_nsmul hz) with h | h <;>
      rw [Multiset.mem_singleton.mp h, Complex.ofReal_im]
  · have hpow : ∀ (p : ℂ[X]) (m : ℕ), (p ^ m).mahlerMeasure = p.mahlerMeasure ^ m := by
      intro p m
      induction m with
      | zero => simp
      | succ m ihm => rw [pow_succ, mahlerMeasure_mul, ihm, pow_succ]
    have h1 := mahlerMeasureZ_X_sq_sub_X_sub_one
    rw [mahlerMeasureZ_eq] at h1 ⊢
    rw [Polynomial.map_pow, hpow, h1, hdeg]
    push_cast
    rw [show (2 * (k : ℝ)) / 2 = (k : ℝ) by ring, rpow_natCast]

/-- **Lehmer's problem for real-rooted integer polynomials** (sharp form): if all complex roots of
`f ∈ ℤ[X]` are real and `M(f) > 1`, then `M(f) ≥ M(X² - X - 1) = (1 + √5)/2`. -/
theorem lehmer_mahler_measure_problem.variants.real_rooted (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0) (hf : mahlerMeasureZ f > 1) :
    mahlerMeasureZ f ≥ mahlerMeasureZ (X ^ 2 - X - 1) := by
  have hinj : Function.Injective (algebraMap ℤ ℂ) := RingHom.injective_int _
  rw [mahlerMeasureZ_X_sq_sub_X_sub_one]
  have hf0 : f ≠ 0 := by
    rintro rfl; norm_num [mahlerMeasureZ, LehmerMahlerMeasureProblem.mahlerMeasure] at hf
  obtain ⟨g, hg, hgreal, h0, h1, hm1, hgf⟩ := exists_reduced _ f rfl hf0 hreal
  rw [← hgf] at hf ⊢
  have hφ2 := goldenRatio_lt_two
  have hgold : (1 + √5) / 2 = goldenRatio := rfl
  rw [hgold]
  rcases (by omega : g.natDegree = 0 ∨ g.natDegree = 1 ∨ 2 ≤ g.natDegree) with hd | hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd, mahlerMeasureZ_eq, Polynomial.map_C, mahlerMeasure_const,
      eq_intCast, Complex.norm_intCast] at hf ⊢
    have : (1 : ℤ) < |g.coeff 0| := by exact_mod_cast hf
    have : (2 : ℝ) ≤ |(g.coeff 0 : ℝ)| := by exact_mod_cast this
    linarith
  · have hdeg : (g.map (algebraMap ℤ ℂ)).degree = 1 := by
      rw [degree_map_eq_of_injective hinj, degree_eq_natDegree hg, hd]; rfl
    rw [mahlerMeasureZ_eq, mahlerMeasure_of_degree_eq_one hdeg, coeff_map, coeff_map, eq_intCast,
      eq_intCast, Complex.norm_intCast, Complex.norm_intCast]
    have hlin := eq_X_add_C_of_natDegree_le_one hd.le
    have c1 : g.coeff 1 ≠ 0 := by
      have := leadingCoeff_ne_zero.mpr hg; rwa [leadingCoeff, hd] at this
    have c0 : g.coeff 0 ≠ 0 := by
      rw [hlin] at h0; simpa using h0
    have cp : g.coeff 1 + g.coeff 0 ≠ 0 := by
      rw [hlin] at h1; simpa using h1
    have cm : -g.coeff 1 + g.coeff 0 ≠ 0 := by
      rw [hlin] at hm1; simpa using hm1
    have key : (2 : ℤ) ≤ max |g.coeff 1| |g.coeff 0| := by
      rcases abs_cases (g.coeff 1) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (g.coeff 0) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rw [ha, hb] <;> omega
    have : (2 : ℝ) ≤ max |(g.coeff 1 : ℝ)| |(g.coeff 0 : ℝ)| := by exact_mod_cast key
    linarith
  · have hs := schinzel_real_rooted g hgreal h0 h1 hm1
    rw [hgold] at hs
    have : goldenRatio ^ (1 : ℝ) ≤ goldenRatio ^ ((g.natDegree : ℝ) / 2) :=
      rpow_le_rpow_of_exponent_le one_lt_goldenRatio.le
        (by rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 1 * 2 ≤ g.natDegree))
    rw [rpow_one] at this
    linarith

/-- Lehmer's problem has a positive answer on the class of real-rooted integer polynomials, with
`μ = M(X² - X - 1) = (1 + √5)/2`; this value is optimal. -/
theorem lehmer_mahler_measure_problem.variants.real_rooted_exists :
    ∃ μ : ℝ, μ > 1 ∧ ∀ f : ℤ[X], (∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0) →
      (mahlerMeasureZ f > 1 → mahlerMeasureZ f ≥ μ) := by
  refine ⟨mahlerMeasureZ (X ^ 2 - X - 1), ?_, fun f hreal hf =>
    lehmer_mahler_measure_problem.variants.real_rooted f hreal hf⟩
  rw [mahlerMeasureZ_X_sq_sub_X_sub_one]
  exact one_lt_goldenRatio

end LehmerMahlerMeasureProblem
