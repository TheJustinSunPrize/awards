# Statement correspondence

## English

The catalogue's exact public wording is:

> Does every dense graph contain a sufficiently dense subgraph whose vertex
degrees are comparable?

The cited Alon paper defines a graph as `D`-balanced when the ratio of its
maximum vertex degree to its minimum vertex degree is at most `D`. It states the
Erdős--Simonovits question in the following quantified form (logarithms in that
section are base 2), and gives a negative answer by Proposition 2.1.

The formal statement used here is the same assertion as the public Formal
Conjectures statement, with the `answer(False)` wrapper made explicit in the
standalone package:

```lean
∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 →
  ∀ᶠ D in atTop, ∀ᶠ n in atTop,
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
        ∃ (H : Subgraph G),
          letI m := H.verts.ncard
          SimpleGraph.IsBalanced H.coe D ∧
            m > (n : ℝ) ^ (1 - α) ∧
            H.edgeSet.ncard > ε * m ^ (1 + α)
```

Here `SimpleGraph.IsBalanced G D` is defined by
`G.maxDegree ≤ D * G.minDegree`. The submitted declaration
`JSP000660.not_jsp_000660` proves the negation of exactly this proposition.
The declaration `JSP000660.answer_false_iff` proves the corresponding literal
`False ↔ target_statement`.

## Source comparison

The source paper's Proposition 2.1 is a stronger construction-level negative
answer: for every fixed `D > 1` and every `n > 10^5`, it supplies a graph with
at most `2n` vertices and at least `2n log(2n)` edges such that every subgraph
whose maximum degree is at most `D` times its average-degree parameter has
average degree bounded by

`36 (4 sqrt(log m) + log(64D) + 18)`.

The Lean proof formalizes the exact quantified target assertion by a simpler
explicit complete bipartite counterexample. It does not claim that the
probabilistic proof text of Proposition 2.1 itself has been line-by-line
translated. This distinction preserves both statement fidelity and attribution.

## Public source links

- [JSP-000660 catalogue entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000660)
- [Alon, Problems and results in extremal combinatorics--II](https://doi.org/10.1016/j.disc.2007.08.090)
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1077.lean)
- [Pinned Lean proof source](https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean)
