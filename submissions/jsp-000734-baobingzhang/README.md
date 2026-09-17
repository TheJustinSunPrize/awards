# JSP-000734: Erdős 883, part (ii): above the ⌊n/2⌋+⌊n/3⌋−⌊n/6⌋ threshold the coprime graph contains every complete tripartite K(1,ℓ,ℓ) (Sárközy)

Catalog entry: [JSP-000734](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000734) · Problem source: [erdosproblems.com/883](https://www.erdosproblems.com/883)

## Problem

For `A ⊆ {1,…,n}` let `G(A)` be the graph on `A` joining coprime integers. (i) If `|A| > ⌊n/2⌋+⌊n/3⌋−⌊n/6⌋`, must `G(A)` contain all odd cycles of length `≤ n/3 + 1`? (ii) Is it true that for every `ℓ ≥ 1`, if `n` is sufficiently large and `|A| > ⌊n/2⌋+⌊n/3⌋−⌊n/6⌋`, then `G(A)` contains a complete tripartite graph `K(1,ℓ,ℓ)` on `2ℓ+1` vertices?

## Scope

Partial progress on Erdős Problem 883 as a whole: question (ii) is formalized in full, i.e. the formal-conjectures statement `erdos_883.parts.ii` (answer `True`) for every fixed `ℓ`, which Sárközy [Sa99] proved (with `ℓ` even growing like `log n / log log log n`). Question (i) (odd cycles; proof claim with a separate Lean formalization by D. Della Pietra, 2026) and Sárközy's growing-`ℓ` quantitative version are not formalized or claimed here.

## Formal statements

All results are in `Erdos883.lean`. `coprimeGraph` and the statement of `erdos_883.parts.ii` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/883.lean`, Apache-2.0), with `answer(True)` replaced by `True`.

```lean
theorem erdos_883.parts.ii : True ↔
    ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ))

theorem erdos_883_parts_ii_direct :
    ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ))
```

`erdos_883.parts.ii : True ↔ ∀ l ≥ 1, ∀ᶠ n in atTop, ∀ A ⊆ Icc 1 n, n/2 + n/3 − n/6 < #A → K(1,l,l).IsContained (coprimeGraph.induce A)` (with `answer(True)` instantiated) and the direct form `erdos_883_parts_ii_direct`, using formal-conjectures' `coprimeGraph` verbatim. `IsContained` is a (not necessarily induced) subgraph embedding.

## Proof outline

Let `S` be the multiples of 2 or 3 in `[1,n]` (so `|S|` is the threshold) and `B` the elements of `A` coprime to 6, `b = |B|`; `A` misses at most `b − 1` elements of `S`. With `ρ(k) = ∏_{p∣k, p≥5}(1 − 1/p)`, a sieve estimate for residue classes mod 6 avoiding a finite set of primes (proved by induction), the moment bound `∑_{k≤N} ρ(k)^{-4} ≤ 55N` and `ρ(k) ≥ 4/(ω+4)` are established. Sparse case `b ≤ n/2^{2ℓ+22}`: choose `x ∈ B` with `b ≤ 220·n·ρ(x)^4`; among disjoint chains `{2u,…,2^ℓ u}` with `u` coprime to `6x`, one lies in `A` with `ρ(u) ≥ ρ(x)/6`; the sieve gives at least `b + ℓ` odd multiples of 3 coprime to `xu`, so `ℓ` of them are in `A`, giving `K(1,ℓ,ℓ)` with centre `x`. Dense case: work modulo `P = r!` for a large `r = r(ℓ)`, group residues into overlapping blocks of 7 classes mod 6 structure; some block has 5 dense classes, and a finite pattern check (by `decide`) yields 3 classes sharing no prime `≤ r`; pairs sharing a prime `> r` are rare, so averaging picks a centre and `K(ℓ,ℓ)` is extracted greedily. This elementary argument for fixed `ℓ` follows Sárközy's split into sparse and dense cases but replaces his analytic lemmas; the thresholds are astronomically large but finite.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos883.erdos_883.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos883.erdos_883_parts_ii_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos883.lean` (`c7cf722baa0d9e7a0ef770d0a36896caec066d9544731009d1df06d39756fe9e`) are in `verification/`.

## Attribution

- Mathematics: A. Sárközy, *Complete tripartite subgraphs in the coprime graph of integers*, Discrete Math. 202 (1999) 227–238 [Sa99], and P. Erdős, A. Sárközy, *On cycles in the coprime graph of integers*, Electron. J. Combin. (1997) [ErSa97], cited by the catalog record JSP-000734 and erdosproblems.com/883. The elementary fixed-`ℓ` argument used in the Lean proof (sieve by induction, moment bound, residue-block pattern) was written during the AI-assisted formalization, following Sárközy's case split.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
