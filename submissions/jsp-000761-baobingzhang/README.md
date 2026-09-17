# JSP-000761: Erdős 917, Dirac's 6-critical graphs with 4n²+8n+3 edges

Catalog entry: [JSP-000761](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000761) · Problem source: [erdosproblems.com/917](https://www.erdosproblems.com/917)

## Problem

Let `f_k(n)` be the maximum number of edges of a graph on `n` vertices which is `k`-critical (chromatic number `k`, and deleting any edge lowers the chromatic number). Is `f_k(n) ≫ n²` for `k ≥ 4`? Is `f_6(n) ~ n²/4`? More generally, is `f_k(n) ~ ½(1 − 1/⌊k/3⌋)n²`?

## Scope

Partial progress: Dirac's construction `f_6(4n + 2) ≥ 4n² + 8n + 3` (the construction behind `f_6(n) ~ n²/4`), and the join-of-odd-cycles construction for `3 ∣ k`, which gives the lower bound behind `½(1 − 1/(k/3))n²`. The asymptotic questions are open and not claimed. Toft's `f_k(n) ≫ n²` for `k ≥ 4` is not formalized.

## Formal statements

All results are in `Erdos917.lean`. `SimpleGraph.IsCriticalEdges` and `SimpleGraph.IsCriticalEdge` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, Apache-2.0). formal-conjectures has no file for Problem 917, so `IsEdgeCritical` and `f` are defined from the erdosproblems.com wording using Mathlib's `chromaticNumber`.

```lean
theorem dirac_construction (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (4 * n + 2)), G.chromaticNumber = 6 ∧
      (∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber = 5) ∧
      G.edgeSet.ncard = 4 * n ^ 2 + 8 * n + 3

theorem exists_isEdgeCritical_six (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (4 * n + 2)), G.IsEdgeCritical 6 ∧
      G.edgeSet.ncard = 4 * n ^ 2 + 8 * n + 3

theorem f_six_ge (n : ℕ) (hn : 1 ≤ n) : 4 * n ^ 2 + 8 * n + 3 ≤ f 6 (4 * n + 2)

theorem exists_isEdgeCritical_three_mul (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (r * (2 * n + 1))), G.IsEdgeCritical (3 * r) ∧
      G.edgeSet.ncard = r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2

theorem f_three_mul_ge (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2 ≤ f (3 * r) (r * (2 * n + 1))
```

For every `n ≥ 1` there is a graph on `4n + 2` vertices with chromatic number 6 in which deleting any edge gives chromatic number exactly 5, with exactly `4n² + 8n + 3` edges. Hence `f 6 (4n+2) ≥ 4n² + 8n + 3`. More generally, the join of `r` copies of `C_{2n+1}` is `3r`-edge-critical with `r(2n+1) + C(r,2)(2n+1)²` edges, so `f (3r) (r(2n+1))` is at least that.

## Proof outline

Vertices `Fin r × ZMod (2n+1)`, with vertices in different copies all adjacent and each copy an odd cycle. Copies need pairwise disjoint colour sets, and an odd cycle needs 3 colours, so `χ = 3r`. Deleting a cycle edge lets that copy use 2 colours after recolouring its unique third-colour vertex. Deleting a cross edge `(a,u)(b,v)` lets `(b,v)` reuse the colour of a vertex in copy `a`. The edge count follows from the handshake lemma (every degree is `2 + (r−1)(2n+1)`). The `sSup` defining `f` is bounded above by the number of possible edges, and the witness is transferred to `Fin` via an equivalence.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos917.dirac_construction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos917.exists_isEdgeCritical_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos917.f_six_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos917.exists_isEdgeCritical_three_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos917.f_three_mul_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos917.lean` (`dbd405f6c649000f8c69d1a936b2c907c813d6ae5ec5845856baff5afd0add4d`) are in `verification/`.

## Attribution

- Mathematics: G. A. Dirac, *A property of 4-chromatic graphs and some remarks on critical graphs*, J. London Math. Soc. 27 (1952), 85–92 [Di52]; P. Erdős [Er69b, Er93] for the problem and the `3 ∣ k` construction.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).
- An unrefereed partial-proof claim by Qiyuan Gu on the erdosproblems.com forum (negative answer to the final question for `k = 12`) is a separate result and is not part of this submission.

No priority for the mathematics is claimed; the contribution is the Lean formalization.
