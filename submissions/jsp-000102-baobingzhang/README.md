# JSP-000102: Erdős 86, the Brass–Harborth–Nienborg C4-free subgraphs of the hypercube

Catalog entry: [JSP-000102](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000102) · Problem source: [erdosproblems.com/86](https://www.erdosproblems.com/86)

## Problem

Let `Q_n` be the `n`-dimensional hypercube (with `2^n` vertices and `n2^{n−1}` edges). Is it true that every subgraph of `Q_n` with `≥ (1/2 + o(1))·n·2^{n−1}` edges contains a `C_4`?

## Scope

Partial progress: the Brass–Harborth–Nienborg lower-bound constructions, i.e. `C_4`-free subgraphs of `Q_n` with `½(n + √n)·2^{n−1}` edges for `n = 4^r`, and `≥ (1/2 + c/√n)·n·2^{n−1}` edges (`c = 1/4`) for every `n ≥ 1`. Erdős's question itself (the matching upper bound) is open and not claimed, and BHN's sharper `0.9√n` constant for general `n` is not formalized.

## Formal statements

All results are in `Erdos86.lean`. `SimpleGraph.hypercube` is copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean`, Apache-2.0); containment and edge counts use Mathlib's `cycleGraph 4 ⊑ H` and `H.edgeSet.ncard`, as in `FormalConjectures/ErdosProblems/86.lean`.

```lean
theorem erdos_86_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      (1 / 2 + c / √n) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ)

theorem bhn_four_pow (n r : ℕ) (hn : n = 4 ^ r) :
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      (H.edgeSet.ncard : ℝ) = 1 / 2 * (n + √n) * 2 ^ (n - 1 : ℕ)

theorem exists_c4Free_subgraph (n : ℕ) (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      4 * H.edgeSet.ncard = 2 ^ n * (n + 2 ^ Nat.log 4 n)
```

For `n = 4^r` there is `H ≤ hypercube n` with `¬ cycleGraph 4 ⊑ H` and exactly `½(n + √n)·2^{n−1}` edges. For every `n ≥ 1` there is a `C_4`-free `H ≤ hypercube n` with `4·|E(H)| = 2^n·(n + 2^{⌊log₄ n⌋})`. Hence `∃ c > 0, ∀ n ≥ 1`, some `C_4`-free subgraph has `≥ (1/2 + c/√n)·n·2^{n−1}` edges.

## Proof outline

Two-colour the edges of `Q_n` so that no square is monochromatic, and take the edges of one colour. On `Q_4`, a colouring with 24 `true` edges (found by computer search and checked by `decide`) splits the edges into classes `e`, `o`, `a`. Replacing each coordinate by a block of four and colouring `e`/`o` edges by the parity of the outer coordinates, and `a` edges by the colour in the smaller cube, gives `Q_{4^r}` with exactly `(4^r + 2^r)/2` `true` edges at every vertex. For general `n`, extra coordinates are added one at a time, with each new direction coloured by parity.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos86.erdos_86_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos86.bhn_four_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos86.exists_c4Free_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos86.lean` (`5d50a6887ac8d985a651f5a1e2ea51df6a35767eaeeef4c9c46318d2b788c07f`) are in `verification/`.

## Attribution

- Mathematics: P. Brass, H. Harborth, H. Nienborg, *On the maximum number of edges in a C4-free subgraph of Qn*, J. Graph Theory 19 (1995), 17–23 [BHN95]; construction as described in B. Stanton, arXiv:1405.5957; problem from P. Erdős [Er91].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
