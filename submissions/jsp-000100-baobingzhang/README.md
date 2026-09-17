# JSP-000100: Erdős 84, first question: the number f(n) of cycle sets of n-vertex graphs is o(2^n)

Catalog entry: [JSP-000100](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000100) · Problem source: [erdosproblems.com/84](https://www.erdosproblems.com/84)

## Problem

The cycle set of a graph `G` on `n` vertices is the set `A ⊆ {3,…,n}` such that `G` has a cycle of length `ℓ` iff `ℓ ∈ A`. Let `f(n)` count the possible such `A`. Prove that `f(n) = o(2^n)`. Prove that `f(n)/2^{n/2} → ∞`.

## Scope

Partial progress on Erdős Problem 84 as a whole: the first question, `f(n) = o(2^n)`, is proved in full (first solved by Verstraëte 2004, improved by Nenadov 2025). The second question (`f(n)/2^{n/2} → ∞`) remains open and is not claimed, and the quantitative bounds `f(n) ≪ 2^{n−n^{1/10}}` (Verstraëte) and `f(n) ≪ 2^{n−n^{1/2−o(1)}}` (Nenadov) are not formalized; the Lean proof uses a simpler argument that gives `f(n) ≤ 3·2^{n−K}` for every fixed `K` and large `n`.

## Formal statements

All results are in `Erdos84.lean`. formal-conjectures has no file for Erdős 84, so `cycleSet` and `numCycleSets` are defined in the file using Mathlib's `SimpleGraph.Walk.IsCycle`; they follow the erdosproblems.com wording (a cycle of length `ℓ` exists iff `ℓ ∈ A`).

```lean
theorem erdos_84 :
    (fun n => (numCycleSets n : ℝ)) =o[Filter.atTop] (fun n => (2 : ℝ) ^ n)

theorem erdos_84_tendsto :
    Filter.Tendsto (fun n => (numCycleSets n : ℝ) / 2 ^ n) Filter.atTop (nhds 0)

theorem erdos_84_eps :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (numCycleSets n : ℝ) ≤ ε * (2 : ℝ) ^ n

theorem eventually_numCycleSets_le (K : ℕ) :
    ∃ N₀, ∀ n, N₀ ≤ n → K ≤ n ∧ numCycleSets n ≤ 3 * 2 ^ (n - K)

theorem cycleSets_finite (n : ℕ) :
    {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSet G = A}.Finite

theorem cycleSet_comap_equiv {V W : Type*} (σ : V ≃ W) (G : SimpleGraph W) :
    cycleSet (G.comap σ) = cycleSet G

theorem two_le_numCycleSets_three : 2 ≤ numCycleSets 3
```

With `cycleSet G = {k | ∃ v (p : G.Walk v v), p.IsCycle ∧ p.length = k}` and `numCycleSets n = ncard {A | ∃ G : SimpleGraph (Fin n), cycleSet G = A}`: `erdos_84 : (fun n => (numCycleSets n : ℝ)) =o[atTop] (fun n => (2 : ℝ)^n)`, with the equivalent forms `erdos_84_tendsto` (`f(n)/2^n → 0`) and `erdos_84_eps`, and the explicit `eventually_numCycleSets_le K : ∃ N₀, ∀ n ≥ N₀, K ≤ n ∧ f(n) ≤ 3·2^{n−K}`. Sanity lemmas: the family is finite (`cycleSets_finite`), cycle sets lie in `{3,…,n}` and are invariant under relabelling (`cycleSet_comap_equiv`, so graphs on `Fin n` represent all `n`-vertex graphs), and `f(3) ≥ 2`.

## Proof outline

Fix `K`, `ℓ = ⌊log₂ n⌋ + 1`, `m = 4(ℓ+K+2)`, `κ = m²+m`, `r = ⌊n/(4ℓ)⌋`. (1) Graphs with no cycle of length `≥ n−K` have cycle sets inside `{3,…,n−K−1}`: at most `2^{n−K}` possibilities. (2) Otherwise relabel so that `0,…,L−1` is a cycle. (3) If at most `r` edges lie off this cycle, the graph is determined by few choices: at most `(n+1)(r+1)(n²+1)^r ≤ 2^{n−K}`. (4) Otherwise either a vertex off the cycle has `κ` neighbours on it, or there are at least `κ³` chords, and two applications of Mirsky's theorem (proved in the file) give `κ` nested, `κ` pairwise disjoint or `κ` pairwise crossing chords; in each case one gets `κ` numbers whose pairwise differences `d` force cycle lengths `d+2` or `L−d`. (5) A greedy double-counting lemma selects `2m` of these numbers with at least `m²/2` distinct differences, so the cycle set contains a prescribed large 'fingerprint'; a union bound over fingerprints gives at most `2^{n−K}`. Altogether `f(n) ≤ 3·2^{n−K}` once `200000(⌊log₂ n⌋+K+3)^7 ≤ n`. This follows the overall strategy of Verstraëte and Nenadov (§5 of arXiv:2501.09904) but replaces their container lemmas by simpler fingerprints that suffice for `o(2^n)`; it was written during the AI-assisted formalization.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos84.erdos_84' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos84.erdos_84_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos84.erdos_84_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos84.eventually_numCycleSets_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos84.cycleSets_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos84.cycleSet_comap_equiv' depends on axioms: [propext, Quot.sound]
'Erdos84.two_le_numCycleSets_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos84.lean` (`50e7ca0ae0db452abebcec52cef8d25a7e36696ac30707b0772113faafb5471e`) are in `verification/`.

## Attribution

- Mathematics: J. Verstraëte, *On the number of sets of cycle lengths*, Combinatorica 24 (2004) 719–730 [Ve04], who first proved `f(n) = o(2^n)`; R. Nenadov, *Improved bound on the number of cycle sets*, arXiv:2501.09904 (2025) [Ne25]; both cited by the catalog record JSP-000100 and erdosproblems.com/84. Problem of Erdős and Faudree [Er94b, Er95, Er96, Er97d]. The simplified fingerprint argument used in the Lean proof was written with AI assistance, following the strategy of [Ve04, Ne25].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
