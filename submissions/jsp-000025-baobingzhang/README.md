# JSP-000025: Lehmer–Mahler measure problem, Schinzel's theorem: M(f) ≥ φ^(deg f/2) for real-rooted f with f(0)f(1)f(−1) ≠ 0, and the sharp Lehmer bound φ for real-rooted integer polynomials

Catalog entry: [JSP-000025](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000025)

## Problem

Lehmer's problem (1933): is there a constant `μ > 1` such that every `f ∈ ℤ[X]` with Mahler measure `M(f) > 1` satisfies `M(f) ≥ μ`? (Catalog JSP-000025: is the Mahler measure of an integer polynomial, whenever greater than one, separated from one by a uniform positive constant?)

## Scope

Partial progress: the special case of polynomials all of whose complex roots are real (totally real algebraic integers), via Schinzel's theorem (1973). Lehmer's problem for general integer polynomials — in particular for reciprocal polynomials, where Lehmer's degree-10 polynomial gives the smallest known measure ≈ 1.17628 — remains open and is not addressed. The non-reciprocal case (Smyth 1971) is also not formalized here.

## Formal statements

All results are in `LehmerSchinzel.lean`. `mahlerMeasure` and `mahlerMeasureZ` are copied verbatim (including docstring) from Google DeepMind's formal-conjectures `FormalConjectures/Wikipedia/LehmerMahlerMeasureProblem.lean` (Apache-2.0); `mahlerMeasure_eq_polynomial_mahlerMeasure` proves agreement with Mathlib's Jensen-integral definition. 'Real-rooted' is `∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0`. Sharpness lemma shows hypotheses are satisfiable in every even degree with equality.

```lean
theorem schinzel_real_rooted (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : f.eval 0 ≠ 0) (h1 : f.eval 1 ≠ 0) (hm1 : f.eval (-1) ≠ 0) :
    ((1 + √5) / 2) ^ ((f.natDegree : ℝ) / 2) ≤ mahlerMeasureZ f

theorem schinzel_real_rooted' (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : f.eval 0 ≠ 0) (h1 : f.eval 1 ≠ 0) (hm1 : f.eval (-1) ≠ 0) :
    ((1 + √5) / 2) ^ ((f.natDegree : ℝ) / 2) ≤ (f.map (algebraMap ℤ ℂ)).mahlerMeasure

theorem schinzel_totally_real (α : ℂ) (hα : IsIntegral ℤ α)
    (htr : ∀ z ∈ ((minpoly ℤ α).map (algebraMap ℤ ℂ)).roots, z.im = 0)
    (h0 : α ≠ 0) (h1 : α ≠ 1) (hm1 : α ≠ -1) :
    ((1 + √5) / 2) ^ (((minpoly ℤ α).natDegree : ℝ) / 2) ≤ mahlerMeasureZ (minpoly ℤ α)

theorem schinzel_real_rooted_sharp (k : ℕ) :
    (∀ z ∈ (((X ^ 2 - X - 1 : ℤ[X]) ^ k).map (algebraMap ℤ ℂ)).roots, z.im = 0) ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval 0 ≠ 0 ∧ ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval 1 ≠ 0 ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).eval (-1) ≠ 0 ∧
      ((X ^ 2 - X - 1 : ℤ[X]) ^ k).natDegree = 2 * k ∧
      mahlerMeasureZ ((X ^ 2 - X - 1) ^ k)
        = ((1 + √5) / 2) ^ ((((X ^ 2 - X - 1 : ℤ[X]) ^ k).natDegree : ℝ) / 2)

theorem mahlerMeasureZ_X_sq_sub_X_sub_one :
    mahlerMeasureZ (X ^ 2 - X - 1) = (1 + √5) / 2

theorem lehmer_mahler_measure_problem.variants.real_rooted (f : ℤ[X])
    (hreal : ∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0) (hf : mahlerMeasureZ f > 1) :
    mahlerMeasureZ f ≥ mahlerMeasureZ (X ^ 2 - X - 1)

theorem lehmer_mahler_measure_problem.variants.real_rooted_exists :
    ∃ μ : ℝ, μ > 1 ∧ ∀ f : ℤ[X], (∀ z ∈ (f.map (algebraMap ℤ ℂ)).roots, z.im = 0) →
      (mahlerMeasureZ f > 1 → mahlerMeasureZ f ≥ μ)

theorem mahlerMeasure_eq_polynomial_mahlerMeasure (p : ℂ[X]) :
    LehmerMahlerMeasureProblem.mahlerMeasure p = Polynomial.mahlerMeasure p
```

With `mahlerMeasure`/`mahlerMeasureZ` copied verbatim from formal-conjectures (`M(f) = ‖a‖ ∏ max(1, ‖αᵢ‖)`, shown equal to Mathlib's integral `Polynomial.mahlerMeasure`): `schinzel_real_rooted` (if all complex roots of `f ∈ ℤ[X]` are real and `f(0), f(1), f(−1) ≠ 0`, then `((1+√5)/2)^(deg f/2) ≤ M(f)`, any leading coefficient, `f` possibly reducible), `schinzel_real_rooted'` (same with Mathlib's Mahler measure), `schinzel_totally_real` (classical form for a totally real algebraic integer `α ∉ {0, ±1}` and its minimal polynomial), `schinzel_real_rooted_sharp` (`(X²−X−1)^k` meets all hypotheses and attains equality), `lehmer_mahler_measure_problem.variants.real_rooted` (real-rooted `f` with `M(f) > 1` has `M(f) ≥ M(X²−X−1) = φ`, optimal) and `...real_rooted_exists` (Lehmer's statement restricted to real-rooted `f`, with `μ = φ`). The `variants.*` names follow the formal-conjectures naming pattern but are our own statements (formal-conjectures has no real-rooted variant).

## Proof outline

Put `e = 1/(2√5)` and `c = 1/2 − e`. For real `x ∉ {0, ±1}`, `max(1,|x|) ≥ φ^(1/2) |x|^c |x²−1|^e` (the function of Höhn–Skoruppa); with `s = x²` or `1/x²` this reduces to `(φ+2) log φ + log s + φ log(1−s) ≤ 0` on `(0,1)`, which follows from `log y ≤ y − 1` and `φ² = φ + 1`. Taking logs and summing over the roots of `f = a ∏(X − αᵢ)`, and using that `|f(0)| = |a|∏|αᵢ|` and `|f(±1)| = |a|∏|αᵢ ∓ 1|` are nonzero integers (≥ 1), gives `log M(f) ≥ (d/2) log φ + c log|a|`. For the Lehmer corollary, factors `X`, `X ∓ 1` are removed without changing `M`, and degrees 0 and 1 are handled directly (`M ≥ 2`).

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'LehmerMahlerMeasureProblem.schinzel_real_rooted' depends on axioms: [propext, Classical.choice, Quot.sound]
'LehmerMahlerMeasureProblem.schinzel_real_rooted'' depends on axioms: [propext, Classical.choice, Quot.sound]
'LehmerMahlerMeasureProblem.schinzel_totally_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'LehmerMahlerMeasureProblem.schinzel_real_rooted_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LehmerMahlerMeasureProblem.mahlerMeasureZ_X_sq_sub_X_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.real_rooted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.real_rooted_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LehmerMahlerMeasureProblem.mahlerMeasure_eq_polynomial_mahlerMeasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`LehmerSchinzel.lean` (`d426fafcc4e6ff372fddef86251f4de18ca7988f792c05f4a99a2e5d563480cb`) are in `verification/`.

## Attribution

- Mathematics: A. Schinzel, On the product of the conjugates outside the unit circle of an algebraic number, Acta Arith. 24 (1973) 385–399, Addendum 26 (1974/75) 329–331; the one-page proof of G. Höhn and N.-P. Skoruppa, Un résultat de Schinzel, J. Théor. Nombres Bordeaux 5 (1993) 185; statement as in C. Smyth, The Mahler measure of algebraic numbers: a survey (2008), §6.1. Lehmer's problem: D. H. Lehmer, Ann. of Math. 34 (1933). The polynomial form (non-monic, reducible f) is a mild generalisation of the same argument. Lean formalization written with AI assistance (Anthropic Claude).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
