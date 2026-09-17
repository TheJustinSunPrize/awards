# JSP-000178: Erdős 184, the K_{3,n−3} lower bound for decompositions into cycles and edges

Catalog entry: [JSP-000178](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000178) · Problem source: [erdosproblems.com/184](https://www.erdosproblems.com/184)

## Problem

Can the edges of every graph on `n` vertices be decomposed into `O(n)` edge-disjoint cycles and single edges? (Erdős–Gallai conjecture.)

## Scope

Partial progress: the lower bound recorded on erdosproblems.com/184, namely that `K_{3,n−3}` shows at least `(1 + c)n` cycles and edges are required for some `c > 0`. This is exactly the formal-conjectures variant `erdos_184.variants.lower_bound`. The `O(n)` upper-bound conjecture and the known upper bounds (`O(n log n)`, Conlon–Fox–Sudakov, Bucić–Montgomery) are not formalized or claimed.

## Formal statements

All results are in `Erdos184.lean`. `SimpleGraph.IsDecomposition` (from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`) and `IsCycleOrEdge` (from `FormalConjectures/ErdosProblems/184.lean`) are copied verbatim from Google DeepMind's formal-conjectures project (Apache-2.0).

```lean
theorem erdos_184.variants.lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop,
      let G : SimpleGraph (Fin n)

lemma four_mul_le (hn : 3 ≤ n) (hG : ∀ v w : Fin n, 3 ≤ (v : ℕ) → (G.Adj v w ↔ (w : ℕ) < 3))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    4 * n ≤ 3 * #D + 12
```

`erdos_184.variants.lower_bound` is proved with its exact formal-conjectures name and statement, with `c = 1/4` (for all `n ≥ 48`), via the explicit inequality `4n ≤ 3·|D| + 12` for every decomposition `D` of `K_{3,n−3}` into cycles and single edges.

## Proof outline

Every vertex on the big side has degree 3 in `G`, while a cycle piece has even degree (0 or 2) at each vertex, so by parity at least one single-edge piece meets each big vertex, and a single edge meets only one big vertex. A cycle piece's degrees on the big side sum to at most 6, since its edges end on the 3 small vertices, each of degree at most 2. Summing gives `#big ≤ #S` and `3·#big ≤ #S + 6·#T`, hence `3|D| ≥ 4(n − 3)`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos184.erdos_184.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos184.four_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos184.lean` (`a4bea46d5babb769a04df346c9ad38e501cb27460fa89f5150ca61c64c7b8b14`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős and T. Gallai (conjecture), see erdosproblems.com/184 [EGP66, Er71, Er76, Er81, Er83b]; the `K_{3,n−3}` example is as stated on erdosproblems.com/184.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
