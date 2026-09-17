# JSP-000117: Erdős 104, Elekes's n^(3/2) lower bound for unit circles through three points

Catalog entry: [JSP-000117](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000117) · Problem source: [erdosproblems.com/104](https://www.erdosproblems.com/104)

## Problem

Given `n` points in the plane, how many unit circles can contain at least three of the points? Erdős asked whether the maximum is `o(n²)` (and, for £100, whether it is `O(n^{3/2})`).

## Scope

Partial progress: Elekes's lower bound, i.e. there are `n`-point sets with `≫ n^{3/2}` unit circles each through at least three of the points. The upper-bound questions (`o(n²)`, `O(n^{3/2})`) are open and not claimed.

## Formal statements

All results are in `Erdos104.lean`. `unitCircleCount`, `possibleUnitCircleCounts` and `maxUnitCircleCount` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/104.lean`, Apache-2.0), with the `ℝ²` notation from `FormalConjecturesForMathlib/Geometry/2d.lean`.

```lean
theorem erdos_104_lower_bound :
    (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) =O[atTop]
      (fun n : ℕ => (maxUnitCircleCount n : ℝ))

theorem rpow_le_maxUnitCircleCount {n : ℕ} (hn : 25 ≤ n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) ≤ 48 * maxUnitCircleCount n

theorem exists_card_eq_choose_two_choose_three_le (m : ℕ) :
    ∃ P : Finset ℝ², P.card = m.choose 2 ∧ m.choose 3 ≤ unitCircleCount P

theorem choose_three_le_maxUnitCircleCount {m n : ℕ} (h : m.choose 2 ≤ n) :
    m.choose 3 ≤ maxUnitCircleCount n
```

For every `m` there is a set of exactly `C(m,2)` planar points with at least `C(m,3)` distinct unit circles each containing at least three of them. Hence `n^{3/2} ≤ 48·maxUnitCircleCount n` for `n ≥ 25`, i.e. `n^{3/2} =O[atTop] maxUnitCircleCount n`, stated with the formal-conjectures definition of `maxUnitCircleCount`.

## Proof outline

Choose unit vectors `u_1,…,u_m` whose subset sums are pairwise distinct (by existence: each new vector avoids finitely many bad values on the infinite unit circle). Take the points `u_a + u_b` (`a < b`) and the centres `u_a + u_b + u_c` (`a < b < c`). Each centre is at distance 1 from the three points `u_a+u_b`, `u_a+u_c`, `u_b+u_c`, and distinct triples give distinct centres. The counted set of unit circles is finite (two circles meet in at most two points) and bounded by `2^n`, so `ncard` and `sSup` are genuine. Pad to exactly `n` points and take `m = ⌊√n⌋`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos104.erdos_104_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos104.rpow_le_maxUnitCircleCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos104.exists_card_eq_choose_two_choose_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos104.choose_three_le_maxUnitCircleCount' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos104.lean` (`f5780a058c2c13b0f9cce1c780f0e7ce8278955a78492f7266c0079af7168870`) are in `verification/`.

## Attribution

- Mathematics: Gy. Elekes, *n points in the plane can determine n^{3/2} unit circles*, Combinatorica 4 (1984), 131 [El84]; problem from P. Erdős [Er75f].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
