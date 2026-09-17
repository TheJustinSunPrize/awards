# JSP-000666: Erdős 809 for every k ≥ 4: χ_S(n, ⌊n²/4⌋+1, C_{2k+1}) ~ n²/8 (Bucić–Chen–Ma 2026)

Catalog entry: [JSP-000666](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000666) · Problem source: [erdosproblems.com/809](https://www.erdosproblems.com/809)

## Problem

Define the anti-Ramsey number `χ_S(n,e,G)` as the smallest `r` such that there is a graph with `n` vertices and `e` edges with an `r`-colouring of its edges in which every copy of `G` has entirely distinct edge colours. Is it true that, for all `k ≥ 3`, `χ_S(n, ⌊n²/4⌋+1, C_{2k+1}) ~ n²/8`?

## Scope

Partial progress: the statement of Erdős Problem 809 is proved for every `k ≥ 4`, which is the theorem of Bucić, Chen and Ma (arXiv:2603.18952, March 2026) cited by the catalog record JSP-000666. The case `k = 3` (`C_7`) remains open and is not claimed, and the paper's general asymptotic formula for all edge counts `e` is not stated (the lower-bound induction `lower_induction` does cover general `e > n²/4`).

## Formal statements

All results are in `Erdos809.lean`. formal-conjectures has no file for Erdős 809; `AllCopiesRainbow` and `chiS` are defined in the file following the erdosproblems.com wording (a graph with `n` vertices and exactly `e` edges; copies are `SimpleGraph.Copy`, i.e. injective homomorphisms; rainbow means injective on the copy's edges). The paper's 'at least `e` edges' gives the same value since deleting edges preserves rainbow copies; that equivalence is not needed and not formalized.

```lean
theorem erdos_809 (k : ℕ) (hk : 4 ≤ k) :
    Tendsto (fun n : ℕ => (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ) /
      (n : ℝ) ^ 2) atTop (𝓝 (1 / 8))

theorem erdos_809_isEquivalent (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ => (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 / 8)

theorem chiS_attained (k n : ℕ) (hk : 1 ≤ k) (hn : 64 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
      ∃ col : G.edgeSet → Fin (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1))),
        AllCopiesRainbow (SimpleGraph.cycleGraph (2 * k + 1)) G col

theorem lower_induction {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (x : ℝ) (hx : 100 ≤ x) (W : Finset V) :
    (W.card : ℝ) ^ 2 / 4 < (sdeg G W : ℝ) / 2 →
      gfun (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2) ≤ R
```

With `AllCopiesRainbow H G col` (every copy `H.Copy G`, i.e. every not-necessarily-induced subgraph embedding, receives pairwise distinct colours) and `chiS n e H := sInf {r | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧ ∃ col : G.edgeSet → Fin r, AllCopiesRainbow H G col}`: `erdos_809 : 4 ≤ k → Tendsto (fun n => chiS n (n²/4+1) (cycleGraph (2k+1)) / n²) atTop (𝓝 (1/8))` and the equivalent `erdos_809_isEquivalent` (`~[atTop] n²/8`). `chiS_attained` shows that for `n ≥ 64` the infimum is attained by an actual graph and colouring (so the value is not the junk `sInf ∅`).

## Proof outline

Upper bound: two disjoint cliques of sizes `⌊n/2⌋ + ⌊√n⌋ + 2` and `n` minus that, trimmed to exactly `⌊n²/4⌋+1` edges; colour the larger clique injectively with `C(a,2)` colours and reuse the palette on the smaller clique; every cycle lies inside one clique, so all copies of `C_{2k+1}` are rainbow, and `C(a,2) = n²/8 + o(n²)`. Lower bound (following Bucić–Chen–Ma): by induction on `n`, for `e > n²/4` the number of colours is at least `e/2 + (n/2)√(e − n²/4) − εn² − C_{k,ε}`. Delete a minimum-degree vertex unless the degree is large; in the dense case, exact-length path lemmas (any two vertices joined by a path of length 4 avoiding a small set, a set `A` of pairwise distance ≤ 3, greedy paths) show that any two edges touching `A` lie on a common `C_{2k+1}` and so get distinct colours; in the sparse case, Mantel's theorem gives a triangle with an edge having at least `δ − n/3` common neighbours (replacing the paper's `n/6` book lemma), used as a parity adjuster. The formalization handles two points not spelled out in the paper: the inductive step when `e − δ ≤ (n−1)²/4`, and Lemma 3.2's inequality for non-integer degree ratios between 2.5 and 3.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos809.erdos_809' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.erdos_809_isEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.chiS_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.lower_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos809.lean` (`7f4fe5e7385dc9d739f65cfa8d285e83ccf0feccf4f06ef88b3727ba9025201e`) are in `verification/`.

## Attribution

- Mathematics: M. Bucić, K. Chen, J. Ma, *On a maximal anti-Ramsey conjecture of Burr, Erdős, Graham, and Sós*, arXiv:2603.18952 (2026) [BCM26], cited by the catalog record JSP-000666 and erdosproblems.com/809; problem of S. A. Burr, P. Erdős, R. L. Graham, V. T. Sós [BEGS89] (J. Graph Theory 13 (1989) 263–282). The Lean proof (written with AI assistance) follows [BCM26] with the modifications described in the outline.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
