# JSP-000105: Erdős 89, Erdős's square-root lower bound for distinct distances

Catalog entry: [JSP-000105](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000105) · Problem source: [erdosproblems.com/89](https://www.erdosproblems.com/89)

## Problem

Does every set of `n` points in `ℝ²` determine `≫ n/√(log n)` distinct distances?

## Scope

Partial progress: Erdős's 1946 elementary lower bound `D ≥ √n/2`, in the sharper integer form `n ≤ 2D² + D + 1`. The conjectured `n/√(log n)` bound and the Guth–Katz bound `n/log n` [GuKa15] are not formalized or claimed.

## Formal statements

All results are in `DistinctDistances.lean`. `distanceSet`, `distinctDistances` and `minimalDistinctDistances` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Geometry/Metric.lean`, Apache-2.0).

```lean
theorem sqrt_isBigO_minimalDistinctDistances :
    (fun (n : ℕ) => Real.sqrt n) =O[atTop] (fun n => (minimalDistinctDistances ℝ² n : ℝ))

theorem le_two_mul_minimalDistinctDistances_sq_add (n : ℕ) :
    n ≤ 2 * minimalDistinctDistances ℝ² n ^ 2 + minimalDistinctDistances ℝ² n + 1

theorem card_le_two_mul_sq_add (A : Finset ℝ²) :
    #A ≤ 2 * distinctDistances A ^ 2 + distinctDistances A + 1

theorem sqrt_div_two_le_minimalDistinctDistances {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt n / 2 ≤ minimalDistinctDistances ℝ² n
```

For every finite planar point set `A` with `D` distinct distances, `#A ≤ 2D² + D + 1`. Hence `minimalDistinctDistances ℝ² n ≥ √n/2` for `n ≥ 2`, and `√n =O[atTop] minimalDistinctDistances ℝ² n`, which is stated in the same `=O[atTop]` shape as the formal-conjectures statements `erdos_89` and `erdos_89.variants.n_dvd_log_n`.

## Proof outline

Fix `p ∈ A`. The other points lie on the `D` circles centred at `p`, so some circle `C` contains `m ≥ (#A − 1)/D` of them. Fix `q ∈ C`. The other `m − 1` points of `C` lie on at most `D` circles centred at `q`, and each of these meets `C` in at most two points (two circles with distinct centres meet in at most two points, `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`). So `m − 1 ≤ 2D`, i.e. `#A − 1 ≤ D(2D + 1)`. The `sInf` in `minimalDistinctDistances` is attained by an actual `n`-point set, so the bound transfers to it.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'DistinctDistances.sqrt_isBigO_minimalDistinctDistances' depends on axioms: [propext, Classical.choice, Quot.sound]
'DistinctDistances.le_two_mul_minimalDistinctDistances_sq_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DistinctDistances.card_le_two_mul_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'DistinctDistances.sqrt_div_two_le_minimalDistinctDistances' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`DistinctDistances.lean` (`8ed83092b9c914fea1a0cdf440fe6cef04f4e5ca0f7a408e8f0eda20bc6e2dce`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53 (1946), 248–250 [Er46b].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
