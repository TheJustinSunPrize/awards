# JSP-000648: Erdős 789, Straus's bound h(n) = O(√n)

Catalog entry: [JSP-000648](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000648) · Problem source: [erdosproblems.com/789](https://www.erdosproblems.com/789)

## Problem

Let `h(n)` be maximal such that every set of `n` integers contains `h(n)` elements for which equal subset sums only occur between subsets with the same number of elements. Estimate `h(n)`.

## Scope

Partial progress: Straus's upper bound `h(n) = O(√n)`, in the explicit form `h(n)² ≤ 6n`. This is the formal-conjectures variant `erdos_789.variants.isBigO_sq`. The matching lower-bound question (for which an unrefereed proof claim by Samuel Korsky, using GPT Astra, is listed on the erdosproblems.com forum) is not claimed.

## Formal statements

All results are in `Erdos789.lean`. `IsSubsetSumSeparatingCard` and `subsetSumThreshold` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/789.lean`, Apache-2.0).

```lean
theorem erdos_789.variants.isBigO_sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n

theorem subsetSumThreshold_sq_le (n : ℕ) : subsetSumThreshold n ^ 2 ≤ 6 * n
```

`erdos_789.variants.isBigO_sq : (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n` is proved with its exact formal-conjectures name and statement, via `subsetSumThreshold n ^ 2 ≤ 6 * n` for every `n`.

## Proof outline

Take `A = {1, …, n}` and a separating subset `B` of size `m`. For each `k ≤ m`, the `k`-element subset sums of `B` take at least `k(m − k) + 1` distinct values (induction on the largest element). By the separating property these value sets are disjoint for different `k` and lie in `[1, m·n]`, so `∑_k (k(m − k) + 1) = (m³ + 5m)/6 ≤ m·n`, giving `m² ≤ 6n`. The set of admissible `m` is nonempty (`B = ∅`) and bounded by `6n`, so `sSup` is attained and inherits the bound.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos789.erdos_789.variants.isBigO_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos789.subsetSumThreshold_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos789.lean` (`df39a05d5772aa33b45bdf0497aae7d841961171a0b3bb6f0d09bf81852ef81f`) are in `verification/`.

## Attribution

- Mathematics: E. G. Straus, *On a problem in combinatorial number theory*, J. Math. Sci. 1 (1966), 77–80 [St66].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
