# Statement and scope

Let G(k) denote the least order forcing a regular induced subgraph of order at least k in every simple graph. The formalized witness on 20 vertices establishes the already-known lower bound G(6) ≥ 21. Here k is the number of vertices, not the common degree.

The exact final declaration in [Graph20Result.lean](Graph20Result.lean) is:

```lean
theorem exists_graph20 : ∃ G : SimpleGraph (Fin 20),
    ∃ inst : DecidableRel G.Adj,
    letI := inst
    ∀ T : Finset (Fin 20), 6 ≤ T.card →
      ∀ d : Nat, ¬ (G.induce (T : Set (Fin 20))).IsRegularOfDegree d
```

The concrete version is `Graph20Proof.graph20_no_regular_induced`. Symmetry, absence of loops, and the bridge between encoded degrees and Mathlib induced-subgraph degrees are proved in Lean. Certificate soundness excludes degrees 0 through 19; the degree bound excludes all higher degrees. The common degree may be zero, and no connectivity condition is imposed. Because the ambient vertex type is finite, the finite-subset quantification covers every vertex subset.

The witness is the first record in Dyson and McKay's [20-vertex sample](https://users.cecs.anu.edu.au/~bdm/data/regsub_ge6.20some.g6.gz). The stored graph6 record, including its trailing newline, has SHA-256 `6bf644663c9126ff2f863348d6bffe5870701c91d019c7a5703044c518729e5a`. It has 20 vertices and 94 edges. The theorem checks the explicit adjacency relation, rather than assuming the external dataset's correctness.

This is not a proof of G(6) = 21, an improved lower bound, or the full open [Erdős #82](https://www.erdosproblems.com/82) conjecture. The mathematical result and construction are credited to Paul W. Dyson and Brendan D. McKay, [arXiv:2604.08215v3, Theorem 1.2](https://arxiv.org/html/2604.08215v3). The additional work is this finite instance's formalization using the verifier credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
