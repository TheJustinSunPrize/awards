# Statement correspondence

## Target and scope

The target is the weak-chromatic interpretation of JSP-000690: existence of a
simple 3-uniform hypergraph that is 3-chromatic-critical and has minimum degree
at least seven. The separate transversal-number criticality result in Li's
paper is outside this submission.

```lean
theorem JSP_000690_full :
    ∃ G : SimpleThreeGraph 9,
      G.edges.length = 22 ∧
      HasChromaticNumber G.edges 3 ∧
      (∀ S : Subhypergraph G, S.IsProper → S.Colorable 2) ∧
      (∀ v : Fin 9, 7 ≤ degree G v) ∧
      (∃ v : Fin 9, degree G v = 7)
```

The fully qualified declaration is `JSP690.JSP_000690_full`.

## Definitions and correspondence

- `Edge n` contains three strictly increasing vertices in `Fin n`, excluding
  repeated vertices. `Edge.ext_vertices` proves equality of canonical edges
  from equality of their vertex membership predicates.
- `SimpleThreeGraph n` requires a duplicate-free edge list. The representation
  thus describes a finite simple 3-uniform hypergraph.
- `Edge.Proper` requires that the three colors are not all equal;
  `Edge.proper_iff_nonmonochromatic` proves this equivalence. This is weak coloring.
- `HasChromaticNumber es k` requires a k-coloring and excludes every q-coloring
  for q < k. Thus the conclusion is exactly three, not just at most three.
- `degree` counts incident edges; the example has degree sequence
  (10,7,7,7,7,7,7,7,7), so the minimum is exactly seven.
- `Subhypergraph` permits an arbitrary retained vertex predicate and any
  duplicate-free subset of edges whose endpoints are retained. `IsProper`
  means that a vertex or edge is missing. Reordering an edge list alone is not
  a proper subhypergraph.
- Subhypergraph colorings have domain `{v : Fin n // S.vertex v}`. Deleting a
  vertex removes whole incident edges. The general restriction lemma
  `proper_subhypergraph_two_colorable` covers all proper subhypergraphs,
  including simultaneous deletion of vertices and edges.
- Vertices 1 through 9 in the paper correspond to 0 through 8 in `Fin 9`.
  The witness uses exactly the 22 edges in Theorem 4.1.
- `binary_obstruction` quantifies over all nine `Fin 2` values. Applying it to
  an arbitrary coloring function covers every binary coloring. Finite proofs
  use `decide`; Python output is not imported as an axiom.

This correspondence is a submitter review of the self-contained definitions,
not an organizer endorsement or a formal equivalence to a separate Mathlib
hypergraph API. The theorem has no external mathematical hypotheses.
