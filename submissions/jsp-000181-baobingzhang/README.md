# JSP-000181: Erdős 188, Tsaturian's theorem: every red/blue colouring of the plane with no red unit pair has a blue unit-spaced 5-term progression (k ≥ 6)

Catalog entry: [JSP-000181](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000181) · Problem source: [erdosproblems.com/188](https://www.erdosproblems.com/188)

## Problem

What is the smallest `k` such that `ℝ²` can be red/blue coloured with no pair of red points unit distance apart, and no `k`-term arithmetic progression of blue points with distance `1`?

## Scope

Partial progress: the best known lower bound `k ≥ 6` (Tsaturian 2017, improving `k ≥ 5` of Erdős–Graham–Montgomery–Rothschild–Spencer–Straus), credited in the catalog record JSP-000181 and on erdosproblems.com/188. Whether a valid colouring exists for some `k` (upper bounds such as Erdős–Graham's claimed `10^7` or later bounds) and the exact value are not formalized or claimed.

## Formal statements

All results are in `Erdos188.lean`. `Set.IsAPOfLengthWith` and `Erdos188.s` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` and `FormalConjectures/ErdosProblems/188.lean`, including the April 2026 fix requiring `‖d‖ = 1`; Apache-2.0).

```lean
theorem tsaturian (blue : Set ℂ)
    (hred : (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1)) :
    ∃ z d : ℂ, ‖d‖ = 1 ∧ ∀ n : ℕ, n < 5 → z + n • d ∈ blue

theorem tsaturian_euclidean (blue : Set (EuclideanSpace ℝ (Fin 2)))
    (hred : (Set.univ \ blue).Pairwise (fun x y => dist x y ≠ 1)) :
    ∃ z d : EuclideanSpace ℝ (Fin 2), ‖d‖ = 1 ∧ ∀ n : ℕ, n < 5 → z + n • d ∈ blue

theorem erdos_188.variants.six_le : ∀ k, k ∈ s → 6 ≤ k

theorem erdos_188.variants.isLeast_six_le (m : ℕ) (hm : IsLeast s m) : 6 ≤ m

theorem erdos_188.variants.estimate_left : ∀ k, k ∈ s → 5 ≤ k
```

`tsaturian : (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) → ∃ z d : ℂ, ‖d‖ = 1 ∧ ∀ n < 5, z + n • d ∈ blue` (Theorem 1.1 of the paper; also `tsaturian_euclidean` in `EuclideanSpace ℝ (Fin 2)`), and with formal-conjectures' `Erdos188.s` and `Set.IsAPOfLengthWith` (verbatim): `erdos_188.variants.six_le : ∀ k ∈ s, 6 ≤ k`, `erdos_188.variants.isLeast_six_le : IsLeast s m → 6 ≤ m`, and `erdos_188.variants.estimate_left : ∀ k ∈ s, 5 ≤ k` (the lower half of formal-conjectures' `erdos_188.variants.estimate`).

## Proof outline

Work in `ℂ` with `ω = e^{iπ/3}`; for a red point `A` and unit `u` encode the lattice `A + (ℤ + ℤω)u` by `f : ℤ × ℤ → Prop`, with the needed closure conditions bundled so that recentring and rotation preserve them. Following Tsaturian: triangle and rotation lemmas (rotation by `θ` with `cos θ = 5/6` moves points at distance `√3` from the centre by exactly 1); a red equilateral triangle of side `√3` forces a red 6-point configuration whose translates by `5ℤ²` are red; if no such triangle exists, the red points lie on lines; in either case a red `A` forces `A + 5` and `A + 5v` red for a suitable unit `v`, a red unit pair. All lattice coordinates are checked by `decide`. The formalization corrects a typo in the paper's Lemma 2.2 (side 3 rather than `√3`, as the proof uses), reads swapped red/blue labels in Lemmas 2.1, 2.2, 2.5 in the evident way, and restructures Lemmas 2.5–2.6 and the final step to prove exactly the needed consequences.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos188.tsaturian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos188.tsaturian_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos188.erdos_188.variants.six_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos188.erdos_188.variants.isLeast_six_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos188.erdos_188.variants.estimate_left' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos188.lean` (`3257010cefa4ea78c79db5039aa2e4e2de7396a29397e04382fd47a166721ce0`) are in `verification/`.

## Attribution

- Mathematics: S. Tsaturian, *A Euclidean Ramsey result in the plane*, Electron. J. Combin. 24 (2017) P4.35 (arXiv:1703.10723) [Ts17], cited by the catalog record JSP-000181 and erdosproblems.com/188; earlier bound by P. Erdős, R. L. Graham, P. Montgomery, B. L. Rothschild, J. Spencer, E. G. Straus [EGMRSS75]; problem of Erdős and Graham [ErGr79, ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
