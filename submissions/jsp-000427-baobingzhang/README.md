# JSP-000427: Erdős 531, the BENTW17 lower bound F(k) ≥ 2^(2^(k−1)/k) for Folkman numbers (with Folkman's theorem)

Catalog entry: [JSP-000427](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000427) · Problem source: [erdosproblems.com/531](https://www.erdosproblems.com/531)

## Problem

Let `F(k)` be the minimal `N` such that if we two-colour `{1,…,N}` there is a set `A` of size `k` such that all subset sums `∑_{a∈S} a` (for `∅ ≠ S ⊆ A`) are monochromatic. Estimate `F(k)`.

## Scope

Partial progress: the lower bound `F(k) ≥ 2^{2^{k−1}/k}` for every `k ≥ 2` of Balogh–Eberhard–Narayanan–Treglown–Wagner (2017), credited in the catalog record JSP-000427, together with Folkman's theorem for two colours (so `F(k)` is a genuine minimum). Estimating `F(k)` remains open; upper bounds and the Erdős–Spencer lower bound are not formalized. The bound is false for `k = 1` (`F(1) = 1`), which the file proves; the paper's 'for all `k`' should read `k ≥ 2`.

## Formal statements

All results are in `Erdos531.lean`. formal-conjectures has no file for Erdős 531; `FolkmanProperty` and `F` follow the erdosproblems.com wording and the phrasing style of formal-conjectures' `532.lean`. Colourings are functions `ℕ → Fin 2`; since only sums in `{1,…,N}` are evaluated, this is equivalent to colouring `{1,…,N}`.

```lean
theorem two_pow_le_F (k : ℕ) (hk : 2 ≤ k) : (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) ≤ F k

theorem two_pow_lt_F (k : ℕ) (hk : 2 ≤ k) : (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) < F k

theorem not_folkmanProperty {k : ℕ} (hk : 2 ≤ k) :
    ¬ FolkmanProperty k ⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊

theorem folkman (k : ℕ) : ∃ N, FolkmanProperty k N

theorem folkmanProperty_iff (k N : ℕ) : FolkmanProperty k N ↔ F k ≤ N

theorem F_one : F 1 = 1

theorem not_two_pow_le_F_one : ¬ (2 : ℝ) ^ ((2 : ℝ) ^ (1 - 1) / 1) ≤ F 1
```

With `FolkmanProperty k N` (every 2-colouring has a `k`-set whose nonempty subset sums all lie in `{1,…,N}` and have one colour) and `F k := sInf {N | FolkmanProperty k N}`: `folkman` (the set is nonempty for every `k`), `folkmanProperty_iff` (`FolkmanProperty k N ↔ F k ≤ N`), `not_folkmanProperty` (for `k ≥ 2` and `n = ⌊2^{2^{k−1}/k}⌋`, some colouring has no good `k`-set), `two_pow_lt_F`/`two_pow_le_F` (`2^{2^{k−1}/k} < F k` for `k ≥ 2`), and `F_one`/`not_two_pow_le_F_one` (`F 1 = 1`, so the bound fails at `k = 1`).

## Proof outline

Folkman's theorem is derived from Mathlib's Hindman theorem (`Hindman.exists_FS_of_finite_cover`) in `ℕ+`, extracting `k` distinct elements with all finite sums monochromatic, and a compactness argument over colourings to pass to a finite interval. The lower bound is a counting version of BENTW17: for `X ⊆ {0,…,n}` colour `x = 2^v·w` (`w` odd) by whether `w ∈ X` agrees with the parity of `v`, so `x` and `2x` always differ. If a `k`-set has two equal subset sums, disjoint parts give sums `x` and `2x`, so no such colouring is good for it. Otherwise, taking `r` of least 2-adic valuation `s`, the `2^{k−1}` pairs `C, C ∪ {r}` produce `2^{k−1}` distinct odd parts that must all lie in or all outside `X`, so at most `2·2^{n+1−2^{k−1}}` sets `X` fail for that `k`-set. A union bound with `2·C(n,k) < n^k ≤ 2^{2^{k−1}}` shows a good colouring exists for `n = ⌊2^{2^{k−1}/k}⌋`, uniformly for all `k ≥ 2`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos531.two_pow_le_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.two_pow_lt_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.not_folkmanProperty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.folkman' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.folkmanProperty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.F_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos531.not_two_pow_le_F_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos531.lean` (`ea9139d91053bfcfae3f99464ffeaceae3c53ba39c189b1b41c1a3bfff0b7bc3`) are in `verification/`.

## Attribution

- Mathematics: J. Balogh, S. Eberhard, B. Narayanan, A. Treglown, A. Z. Wagner, *An improved lower bound for Folkman's theorem*, Bull. London Math. Soc. 49 (2017) 745–747 [BENTW17] (arXiv:1703.02473), cited by the catalog record JSP-000427 and erdosproblems.com/531; J. Folkman (Folkman's theorem); problem of Erdős [ErSp89]. The counting presentation and the uniform treatment of all `k ≥ 2` were written during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
