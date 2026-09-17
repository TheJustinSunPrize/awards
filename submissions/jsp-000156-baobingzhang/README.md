# JSP-000156: Erdős 158, the Sidon-set case: liminf |A∩[0,N)|·√(log N / N) < ∞ for infinite Sidon sets

Catalog entry: [JSP-000156](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000156) · Problem source: [erdosproblems.com/158](https://www.erdosproblems.com/158)

## Problem

Let `A ⊂ ℕ` be an infinite set such that for every `n` there are at most 2 solutions of `a + b = n` with `a ≤ b` (a `B₂[2]` set). Must `liminf_{N→∞} |A ∩ {1,…,N}| / N^{1/2} = 0`?

## Scope

Partial progress: only the Sidon-set special case (at most one representation), which is the case credited in the catalog record JSP-000156. The `B₂[2]` question asked by the problem remains open and is not claimed.

## Formal statements

All results are in `Erdos158.lean`. `IsSidon` is copied verbatim from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`, and the statements of `erdos_158.variants.isSidon'` and `erdos_158.variants.isSidon` (with the proof of the latter) from `FormalConjectures/ErdosProblems/158.lean`, Google DeepMind's formal-conjectures project (Apache-2.0). The same Lean argument is also submitted, restated with the `[1, x]` normalisation, for JSP-000996 (Erdős 1191), where the catalog credits the same theorem.

```lean
theorem erdos_158.variants.isSidon' {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    liminf (fun N ↦ ENNReal.ofReal ((A ∩ .Iio N).ncard * N ^ (- 1 / 2 : ℝ) * log N ^ (1 / 2 : ℝ)))
      atTop < ⊤

theorem erdos_158.variants.isSidon {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0
```

`erdos_158.variants.isSidon'`: for every infinite Sidon set `A ⊆ ℕ`, `liminf_N ENNReal.ofReal(|A ∩ [0, N)| · N^{−1/2} · (log N)^{1/2}) < ⊤` (Erdős), and `erdos_158.variants.isSidon`: `liminf_N |A ∩ [0, N)| · N^{−1/2} = 0`. Both have their exact formal-conjectures names and statements; the derivation of `isSidon` from `isSidon'` is the one in formal-conjectures.

## Proof outline

Split `[0, N²)` into `N` blocks of length `N` with counts `F_ℓ`. For a Sidon set, ordered differences of pairs inside the same block are distinct and lie in `(−N, N)`, so `∑ F_ℓ² ≤ 5N`. Cauchy–Schwarz with weights `1/√(ℓ+1)` gives `(∑ F_ℓ/√(ℓ+1))² ≤ 5N(1 + log N)`. If `A(x) > C√(x/log x)` for all large `x`, Abel summation gives `∑ F_ℓ/√(ℓ+1) ≫ C√N (log N − 1)/√(log N)`, and squaring contradicts the previous bound for `C = 100` and large `N`. Hence `A(M)·√(log M) ≤ 100·√M` for arbitrarily large `M`, which gives the finite liminf. The `liminf = 0` statement follows since `√(log N) → ∞`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos158.erdos_158.variants.isSidon'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos158.erdos_158.variants.isSidon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos158.lean` (`c82540706793bbc02d11872a07990ad08f48cf2b8eb0788be48f9af6305db116`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős (Sidon-set bound, see H. Halberstam and K. F. Roth, *Sequences*, Vol. I, 1966, Ch. II), as cited on erdosproblems.com/158 and in formal-conjectures ([ESS94] P. Erdős, A. Sárközy, V. T. Sós, *On sum sets of Sidon sets, I*, J. Number Theory 47 (1994), 329–347).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
