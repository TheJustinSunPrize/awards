# JSP-000544: Erdős 670, the one-dimensional case (Erdős)

Catalog entry: [JSP-000544](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000544) · Problem source: [erdosproblems.com/670](https://www.erdosproblems.com/670)

## Problem

Let `A ⊆ ℝ^d` be a set of `n` points such that all pairwise distances differ by at least 1. Is the diameter of `A` at least `(1 + o(1))n²`?

## Scope

Partial progress: the case `d = 1`, which erdosproblems.com/670 records as proved by Erdős [Er97f]. Fixed `d ≥ 2` is open and not claimed; Ho's high-dimensional counterexample [Ho26] is not formalized.

## Formal statements

All results are in `Erdos670.lean`. formal-conjectures has no file for Problem 670; `DistancesSeparated` (distinct unordered pairs via `Sym2`) and `Erdos670Statement d` (fixed `d`, `(1 + o(1))n²` written as `∃ f → 0`) are defined directly from the erdosproblems.com wording, using `Metric.diam`.

```lean
theorem erdos_670_dim_one : Erdos670Statement 1

theorem erdos_670_real :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ A : Finset ℝ, #A = n → DistancesSeparated A →
        (1 + f n) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set ℝ)

theorem erdos_670_real_eps :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ, #A = n → DistancesSeparated A →
      (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set ℝ)

theorem mul_sub_one_le_diam (A : Finset ℝ) (hA : DistancesSeparated A) (k : ℕ) (hk : k ≤ #A) :
    ((k : ℝ) * #A - k * (k + 1) / 2) * ((k : ℝ) * #A - k * (k + 1) / 2 - 1) ≤
      k * (k + 1) * Metric.diam (A : Set ℝ)

theorem exists_distancesSeparated (n : ℕ) : ∃ A : Finset ℝ, #A = n ∧ DistancesSeparated A
```

For `d = 1` (both in `EuclideanSpace ℝ (Fin 1)` and in `ℝ`): if `A` has `n` points whose pairwise distances (over distinct unordered pairs) differ by at least 1, then `diam A ≥ (1 + f(n))n²` for some `f → 0`, and in explicit form `(k n − k(k+1)/2)(k n − k(k+1)/2 − 1) ≤ k(k+1)·diam A` for all `k ≤ n`. The hypotheses are satisfiable for every `n` (powers of two).

## Proof outline

Sort the points `x_1 < ⋯ < x_n` and fix `k`. The `m = kn − k(k+1)/2` pairs with index span at most `k` have 1-separated distances, so their sum is at least `m(m−1)/2`. For each span `j ≤ k`, telescoping gives `∑_i (x_{i+j} − x_i) ≤ j·diam A`, so the sum is at most `k(k+1)·diam A/2`. Taking `k = ⌈2/ε⌉` yields `diam A ≥ (1 − ε)n²` for large `n`, which is equivalent to the `(1 + o(1))n²` form.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos670.erdos_670_dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.erdos_670_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.erdos_670_real_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.mul_sub_one_le_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos670.exists_distancesSeparated' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos670.lean` (`b75462d1182713cb8b24087142ee594598bc0394eefad7f4152651442e75d3aa`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, *Some unsolved problems*, Combinatorics, geometry and probability (Cambridge, 1993) (1997), 1–10 [Er97f] (the case `d = 1`); related: Ho, arXiv:2604.15305 [Ho26].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
