# JSP-000487: Erdős 600, the Ruzsa–Szemerédi bound e(n,r) = o(n²)

Catalog entry: [JSP-000487](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000487) · Problem source: [erdosproblems.com/600](https://www.erdosproblems.com/600)

## Problem

Let `e(n, r)` be the least `e` such that every graph on `n` vertices with at least `e` edges, each of which lies in a triangle, has an edge contained in at least `r` triangles. Erdős asked for the behaviour of `e(n, r)` (e.g. whether `e(n, r+1) − e(n, r) → ∞`).

## Scope

Partial progress: the Ruzsa–Szemerédi theorem `e(n, r) = o(n²)` for every fixed `r`, which is the formal-conjectures variant `erdos_600.variants.ruzsa_szemeredi_upper_bound`. The open questions of Problem 600 are not claimed.

## Formal statements

All results are in `Erdos600.lean`. `Erdos600Prop`, `eFunction` and `SimpleGraph.trianglesContaining` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/600.lean` and `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean`, Apache-2.0).

```lean
theorem erdos_600.variants.ruzsa_szemeredi_upper_bound :
    ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n : ℝ)^2)

theorem erdos600Prop_ceil (r n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hn : (r : ℝ) < triangleRemovalBound (ε / (6 * (r + 1))) * n) :
    Erdos600Prop n ⌈ε * (n : ℝ) ^ 2⌉₊ r
```

`erdos_600.variants.ruzsa_szemeredi_upper_bound : ∀ r, (fun n ↦ (eFunction n r : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)^2)` is proved with its exact formal-conjectures name and statement, together with the explicit estimate `Erdos600Prop n ⌈ε n²⌉₊ r` whenever `r < δ(ε/(6(r+1)))·n`, where `δ` is Mathlib's triangle-removal bound.

## Proof outline

Assume every edge lies in fewer than `r` triangles. Then there are at most `r·n²` triangles, which is below the removal threshold, so Mathlib's triangle removal lemma yields a triangle-free subgraph obtained by deleting fewer than `ε' n²` edges `D`. Every triangle contains an edge of `D`, so every edge of `G` lies in a triangle through some `d ∈ D`, giving `#E ≤ 6r·#D < ε n² ≤ #E`, a contradiction. The `sInf` defining `eFunction` is bounded by exhibiting `⌈ε n²⌉₊` as a member, and letting `ε → 0` gives the `o(n²)` bound.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos600.erdos600Prop_ceil' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos600.lean` (`bd504afde12ba082b51f7cde8f8f3f88cd2c3023f6a6f846b22233cec109c223`) are in `verification/`.

## Attribution

- Mathematics: I. Z. Ruzsa and E. Szemerédi, *Triple systems with no six points carrying three triangles*, Combinatorics (Keszthely, 1976), Vol. II (1978), 939–945 [RuSz78]; the triangle removal lemma is used from Mathlib.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
