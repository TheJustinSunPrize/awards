# JSP-000867: Erdős 1045, the regular polygon does not maximise the distance product for n = 4 and n = 6

Catalog entry: [JSP-000867](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000867) · Problem source: [erdosproblems.com/1045](https://www.erdosproblems.com/1045)

## Problem

Let `z_1,…,z_n ∈ ℂ` with `|z_i − z_j| ≤ 2` for all `i, j`, and `Δ(z_1,…,z_n) = ∏_{i≠j} |z_i − z_j|`. What is the maximum possible value of `Δ`? Is it maximised by taking the `z_i` to be the vertices of a regular polygon?

## Scope

Partial progress: the answer to the regular-polygon question is negative for `n = 4` and `n = 6`, via explicit configurations. The maximum value of `Δ`, the general even case (claimed by Cambie) and the odd case are not formalized or claimed.

## Formal statements

All results are in `DistanceProduct.lean`. formal-conjectures has no file for Problem 1045, so `delta`, `DiamLeTwo`, `regularPolygon` and `IsRegularPolygon` are defined directly from the erdosproblems.com wording (`Δ` over ordered pairs `i ≠ j`, diameter at most 2).

```lean
theorem not_regularPolygonMaximises_four_and_six :
    ¬ RegularPolygonMaximises 4 ∧ ¬ RegularPolygonMaximises 6

theorem erdos_1045_four :
    ∃ z : Fin 4 → ℂ, DiamLeTwo z ∧
      ∀ w : Fin 4 → ℂ, IsRegularPolygon w → DiamLeTwo w → delta w < delta z

theorem erdos_1045_six :
    ∃ z : Fin 6 → ℂ, DiamLeTwo z ∧
      ∀ w : Fin 6 → ℂ, IsRegularPolygon w → DiamLeTwo w → delta w < delta z

theorem delta_kite : delta kite = 2 ^ 12 * (2 - √3) ^ 2

theorem delta_reuleauxSix : delta reuleauxSix = 2 ^ 33 * (2 - √3) ^ 9
```

For `n = 4` the kite `0, √3 ± i, 2` has diameter 2 and `Δ = 2^12(2 − √3)^2 ≈ 294.08 > 4^4`, and for `n = 6` the Reuleaux-triangle vertices plus arc midpoints have diameter 2 and `Δ = 2^33(2 − √3)^9 ≈ 1.3109·6^6`. Every regular 4-gon or 6-gon (any centre, radius, rotation or labelling) satisfying the constraint has `Δ ≤ n^n`, attained by the unit square and unit hexagon. Hence the regular polygon is not a maximiser for `n = 4` and `n = 6`.

## Proof outline

Explicit coordinates in `ℚ(√3)`. The diameter constraints and the exact values of `Δ` are proved by expanding squared distances with `Real.sq_sqrt` and `nlinarith`/`norm_num`. For regular polygons `c + a·e^{2πik/n}`, the constraint forces `|a| ≤ 1`, and `Δ = |a|^{n(n−1)}·n^n`, so `Δ ≤ n^n`. The comparison `n^n < Δ` reduces to numeric inequalities for `2 − √3`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1045.not_regularPolygonMaximises_four_and_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1045.erdos_1045_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1045.erdos_1045_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1045.delta_kite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1045.delta_reuleauxSix' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`DistanceProduct.lean` (`aaabb812e229618c244cbd62b0fe8975e79458c5c0096b66e33a584f772e194f`) are in `verification/`.

## Attribution

- Mathematics: T. Hu and Q. Tang (the `n = 4` kite and an `n = 6` example, erdosproblems.com forum, 2025); S. Cambie, T. Decadt, Z. Dong, T. Hu, Q. Tang, arXiv:2603.07088 (2026) (the `n = 6` configuration, Table 1); problem from P. Erdős, F. Herzog, G. Piranian [EHP58].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
