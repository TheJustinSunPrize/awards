# JSP-000149: Erdős 149, Chung–Gyárfás–Tuza–Trotter: graphs with maximum degree D and no two strongly independent edges have at most 5D²/4 edges (sharp)

Catalog entry: [JSP-000149](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000149) · Problem source: [erdosproblems.com/149](https://www.erdosproblems.com/149)

## Problem

The strong chromatic index `sq(G)` is the minimum `k` such that the edges of `G` can be partitioned into `k` sets of strongly independent edges (each inducing a matching). Is it true that `sq(G) ≤ (5/4)Δ²` for every graph with maximum degree `Δ`? Erdős and Nešetřil also asked the easier question whether every graph with more than `(5/4)Δ²` edges contains two strongly independent edges.

## Scope

Partial progress: the 'easier' Erdős–Nešetřil question is answered in full by the Chung–Gyárfás–Tuza–Trotter theorem (1990), credited in the catalog record JSP-000149: a graph with maximum degree `≤ D` and no two strongly independent edges has at most `5D²/4` edges (`(5D²−2D+1)/4` for odd `D`), attained by blow-ups of `C_5`. The main conjecture `sq(G) ≤ (5/4)Δ²` remains open and is not claimed (the file only derives it for graphs with no strongly independent pair); the uniqueness of the extremal graph is not formalized.

## Formal statements

All results are in `Erdos149.lean`. formal-conjectures has no file for Erdős 149; `StronglyIndependent`, `IsStrongEdgeColoring` and `cgttBound` are defined in the file following the erdosproblems.com wording; `free2K2_iff` shows the internal `Free2K2` notion is equivalent to having no strongly independent pair.

```lean
theorem card_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) :
    #G.edgeFinset ≤ cgttBound D

theorem card_edgeFinset_le_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) : #G.edgeFinset ≤ cgttBound G.maxDegree

theorem erdos_149_easier (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 < (#G.edgeFinset : ℝ)) :
    ∃ e₁ e₂, StronglyIndependent G e₁ e₂

theorem erdos_149_easier_at_least_false :
    ¬∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (5 / 4 : ℝ) * (H.maxDegree : ℝ) ^ 2 ≤ (#H.edgeFinset : ℝ) →
        ∃ e₁ e₂, StronglyIndependent H e₁ e₂

theorem blowup_sizes_extremal (D : ℕ) :
    (blowup (sizes D)).maxDegree = D ∧
      (∀ e₁ e₂, ¬StronglyIndependent (blowup (sizes D)) e₁ e₂) ∧
      #(blowup (sizes D)).edgeFinset = cgttBound D

theorem exists_isStrongEdgeColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) :
    ∃ c : G.edgeSet → Fin (cgttBound G.maxDegree), IsStrongEdgeColoring G c

theorem card_le_of_isStrongEdgeColoring_blowup (D k : ℕ)
    (c : (blowup (sizes D)).edgeSet → Fin k) (hc : IsStrongEdgeColoring _ c) :
    cgttBound D ≤ k

lemma four_mul_cgttBound_le (D : ℕ) : 4 * cgttBound D ≤ 5 * D ^ 2
```

With `StronglyIndependent G e₁ e₂` (both edges, all four endpoint pairs distinct and non-adjacent), `IsStrongEdgeColoring` and `cgttBound D = 5D²/4` (even `D`), `(5D²−2D+1)/4` (odd `D`): `card_edgeFinset_le : (∀ v, deg v ≤ D) → (∀ e₁ e₂, ¬ StronglyIndependent G e₁ e₂) → #E(G) ≤ cgttBound D` for every `D` (no connectivity assumption), `card_edgeFinset_le_maxDegree`, `erdos_149_easier : (5/4)Δ² < #E(G) → ∃ e₁ e₂, StronglyIndependent G e₁ e₂`, `erdos_149_easier_at_least_false` (the page's literal 'at least' wording is refuted by `C_5`), `blowup_sizes_extremal` (the `C_5` blow-up with parts `⌈D/2⌉,⌈D/2⌉,⌊D/2⌋,⌊D/2⌋,⌊D/2⌋` has maximum degree `D`, no strongly independent pair and exactly `cgttBound D` edges), `exists_isStrongEdgeColoring` and `card_le_of_isStrongEdgeColoring_blowup` (links to the strong chromatic index; `5/4` cannot be lowered).

## Proof outline

Following Chung–Gyárfás–Tuza–Trotter (Discrete Math. 81 (1990) 129–135), split by clique number. Bipartite graphs have at most `D²` edges (Theorem 1). Triangle-free non-bipartite graphs are `C_5` blow-ups plus isolated vertices (Theorem 2, proved here by fixing an edge and either finding an induced `C_5` to which every vertex attaches as in a blow-up, or building an explicit bipartition), and an integer optimisation gives `cgttBound D`. If `ω ≥ 5`, a 5-clique gives `4|E| ≤ 5D² − 5D − 20`; if `ω = 4`, a dominating clique (Theorem 3) and the bipartite argument on edges of type (1,2) give `4|E| ≤ 5D² − 3D − 10`; if `ω = 3`, Claims 1–7 of the paper bound the edges. Isolated vertices are handled throughout.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos149.card_edgeFinset_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.card_edgeFinset_le_maxDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.erdos_149_easier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.erdos_149_easier_at_least_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.blowup_sizes_extremal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.exists_isStrongEdgeColoring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.card_le_of_isStrongEdgeColoring_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos149.four_mul_cgttBound_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos149.lean` (`a47ad8d1b6d61a37e44c6084e0de70f5b8ff840faab6386bf7c66446323b8663`) are in `verification/`.

## Attribution

- Mathematics: F. R. K. Chung, A. Gyárfás, Zs. Tuza, W. T. Trotter, *The maximum number of edges in 2K₂-free graphs of bounded degree*, Discrete Math. 81 (1990) 129–135 [CGTT90], cited by the catalog record JSP-000149; problem of Erdős and Nešetřil (1985). Some case arguments (the triangle-free case and the `ω = 4, 5` counting) were restructured during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
