# JSP-000165: Erdős 168, Graham–Spencer–Witsenhausen: lim F(N)/N exists for sets avoiding {n, 2n, 3n}

Catalog entry: [JSP-000165](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000165) · Problem source: [erdosproblems.com/168](https://www.erdosproblems.com/168)

## Problem

Let `F(N)` be the size of the largest subset of `{1, …, N}` which does not contain any set of the form `{n, 2n, 3n}`. What is `lim_{N→∞} F(N)/N`? Is this limit irrational?

## Scope

Partial progress: existence of the limit (Graham–Spencer–Witsenhausen 1977), the formal-conjectures variant `erdos_168.variants.limit_exists`. The value of the limit (numerically 0.800965…) and its irrationality, i.e. `erdos_168.parts.i` and `erdos_168.parts.ii`, are not formalized or claimed.

## Formal statements

All results are in `Erdos168.lean`. `NonTernary`, `IntervalNonTernarySets`, `F`, the lemmas `F_0`–`F_3`, `mem_IntervalNonTernarySets_iff` and the statement of `erdos_168.variants.limit_exists` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/168.lean`, Apache-2.0).

```lean
theorem erdos_168.variants.limit_exists :
    ∃ x, Filter.Tendsto (fun N => (F N / N : ℝ)) Filter.atTop (𝓝 x)
```

`erdos_168.variants.limit_exists : ∃ x, Tendsto (fun N => (F N / N : ℝ)) atTop (𝓝 x)` is proved with its exact formal-conjectures name and statement, using the formal-conjectures definitions `NonTernary`, `IntervalNonTernarySets` and `F`.

## Proof outline

Write `n = κ(n)·τ(n)` with `κ(n)` coprime to 6 and `τ(n)` 3-smooth. Every triple `{n, 2n, 3n}` lies in one fibre `κ = k`, so the maximum splits as a sum over fibres, and each fibre `{x ≤ N : κ x = k}` is `k` times a set of 3-smooth numbers, on which the maximum is scale invariant. Hence `F(m+1) − F(m) = c(m) ∈ {0, 1}` depends only on `τ(m+1)`, and `c(m + 6^K) = c(m)` unless `2^K ∣ m+1` or `3^K ∣ m+1`. Truncating `c` on those indices gives a `6^K`-periodic sequence whose Cesàro means converge, and the truncation changes `F(N)` by at most `N/2^K + N/3^K`. So `F(N)/N` is a Cauchy sequence and converges.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos168.erdos_168.variants.limit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos168.lean` (`ac10b41382f67f734f36d86a3df0a640e165f72fd4b5c1a9bdc98b40d993605a`) are in `verification/`.

## Attribution

- Mathematics: R. L. Graham, J. Spencer, H. S. Witsenhausen, *On extremal density theorems for linear forms*, in Number Theory and Algebra (1977) [GSW77], as cited by the catalog record JSP-000165 and erdosproblems.com/168. Problem from Erdős–Graham [ErGr79, ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
