# JSP-000543: Erdős 669, the orchard problem for k = 3: f₃(n), F₃(n) = n²/6 − O(n), so both limits after division by n² equal 1/6 (Burr–Grünbaum–Sloane)

Catalog entry: [JSP-000543](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000543) · Problem source: [erdosproblems.com/669](https://www.erdosproblems.com/669)

## Problem

Let `F_k(n)` be minimal such that for any `n` points in `ℝ²` there are at most `F_k(n)` distinct lines passing through at least `k` of the points, and `f_k(n)` similarly with exactly `k` points. Estimate `f_k(n)` and `F_k(n)`; in particular determine `lim F_k(n)/n²` and `lim f_k(n)/n²`.

## Scope

Partial progress: the case `k = 3` (the classical orchard problem) is proved in full as credited to Burr–Grünbaum–Sloane on erdosproblems.com/669 and in the catalog record JSP-000543: `f_3(n) = n²/6 − O(n)`, `F_3(n) = n²/6 − O(n)`, hence both limits equal `1/6`; together with the trivial bound `F_k(n)·C(k,2) ≤ C(n,2)` for all `k ≥ 2`. The limits for `k ≥ 4` remain open and are not claimed; BGS's exact value `1 + ⌊n(n−3)/6⌋` and their sharper upper bounds are not formalized.

## Formal statements

All results are in `Erdos669.lean`. formal-conjectures has no file for Erdős 669; `IsLine` is copied from formal-conjectures' `FormalConjectures/ErdosProblems/209.lean` (Apache-2.0), `ℝ²` is `EuclideanSpace ℝ (Fin 2)`, and `F`, `f` follow the erdosproblems.com wording literally (all lines of the plane are counted).

```lean
theorem erdos_669.variants.three :
    Tendsto (fun n => (F 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6)) ∧
      Tendsto (fun n => (f 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6))

theorem erdos_669.variants.three_isBigO :
    (fun n => (f 3 n : ℝ) - n ^ 2 / 6) =O[atTop] (fun n => (n : ℝ)) ∧
      (fun n => (F 3 n : ℝ) - n ^ 2 / 6) =O[atTop] (fun n => (n : ℝ))

theorem bounds_three (n : ℕ) :
    ((n : ℝ) ^ 2 - 4 * n) / 6 ≤ f 3 n ∧ (f 3 n : ℝ) ≤ F 3 n ∧ (F 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6

theorem erdos_669.variants.upper {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    F k n * k.choose 2 ≤ n.choose 2

theorem f_le_F {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : f k n ≤ F k n

theorem isGreatest_F {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsGreatest {x | ∃ S : Finset ℝ², S.card = n ∧ (richLines k S).ncard = x} (F k n)

theorem isGreatest_f {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsGreatest {x | ∃ S : Finset ℝ², S.card = n ∧ (exactLines k S).ncard = x} (f k n)

theorem richLines_finite {k : ℕ} (hk : 2 ≤ k) (S : Finset ℝ²) : (richLines k S).Finite
```

With `richLines k S` / `exactLines k S` (lines of `ℝ²` meeting `S` in at least / exactly `k` points) and `F k n`, `f k n` defined as in the problem ('minimal such that every `n`-point set has at most that many lines'), proved to be genuine maxima (`isGreatest_F`, `isGreatest_f`, `richLines_finite` for `k ≥ 2`): `erdos_669.variants.three : F 3 n / n² → 1/6 ∧ f 3 n / n² → 1/6`, `erdos_669.variants.three_isBigO : f 3 n − n²/6 = O(n) ∧ F 3 n − n²/6 = O(n)`, `bounds_three : (n² − 4n)/6 ≤ f 3 n ≤ F 3 n ≤ n²/6`, `erdos_669.variants.upper : 2 ≤ k → F k n · C(k,2) ≤ C(n,2)`, `f_le_F`.

## Proof outline

Upper bound: two distinct points lie on exactly one line, so double counting ordered pairs gives `#lines · k(k−1) ≤ n(n−1)`. Lower bound (following the idea of [BGS74] — points on a cubic whose group law is a circle, collinear iff parameters sum to 0 mod `m` — but on the singular cubic `y(1+x²) = 1` with a tangent parametrization): three points `(t, 1/(1+t²))` are collinear iff `st + su + tu = 1`, no line meets the curve in 4 of them, and with `t_j = tan(π/6 + πj/m)` (`m = n` or `n+1`, `3 ∤ m`) the condition `m ∣ a + b + c` gives `e₂ = 1`. Counting shows at least `n² − 4n` ordered pairs extend to a third point, and each 3-point line arises from at most 6 pairs, so `f_3(n) ≥ (n² − 4n)/6`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos669.erdos_669.variants.three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.erdos_669.variants.three_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.bounds_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.erdos_669.variants.upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.f_le_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.isGreatest_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.isGreatest_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos669.richLines_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos669.lean` (`c2bb36403a621ae94656714d8b0810c7098b968dd7de048fb37d1edccaaea16b`) are in `verification/`.

## Attribution

- Mathematics: S. A. Burr, B. Grünbaum, N. J. A. Sloane, *The orchard problem*, Geom. Dedicata 2 (1974) 397–424 [BGS74], cited by the catalog record JSP-000543 and erdosproblems.com/669; the orchard problem goes back to Sylvester; problem of Erdős [Er97f]. The specific curve and parametrization used in the Lean proof were chosen during the AI-assisted formalization, following the BGS idea.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
