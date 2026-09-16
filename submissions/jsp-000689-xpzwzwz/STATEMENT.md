# Statement alignment and scope

JSP-000689 corresponds to Erdős Problem #833. Its primary question asks for
an absolute positive `c` such that each three-chromatic, `r`-uniform hypergraph
with `r ≥ 2` has a vertex in at least `(1+c)^r` edges.

## Definitions

- `V` is any finite vertex type. The proof does not assume a graph embedding,
  extra graph structure, an ordering, or a degree bound as part of the target.
- `H : Finset (Finset V)` is an ordinary finite simple hypergraph: an edge is a
  finite set of vertices, and duplicate edges are not counted.
- Uniformity is literally `∀ e ∈ H, e.card = r`.
- `Mono e c` states that every pair of vertices of `e` has the same Boolean
  colour. Negating this means that `e` contains both colours.
- `NotTwoColorable H` means there is no Boolean colouring with no monochromatic
  edge. This is weaker than assuming chromatic number exactly three, so our
  theorem applies in particular to every three-chromatic hypergraph.
- `degree H v` is the cardinality of the actual incident-edge filter
  `{e ∈ H | v ∈ e}`.

## Quantifiers and boundaries

`erdos833` is proved for every finite vertex type, every finite edge family,
and every `r ≥ 2`. Its conclusion uses the ordinary real power
`(1 + 1/8 : ℝ)^r`, compared with the natural degree cast to the reals.

`prize_statement` explicitly quantifies a single real constant *before* all
vertex counts, ranks, and hypergraphs. The witness is `1/8`.
All small ranks `2,3,4,5` are handled, so there is no implicit sufficiently-large
assumption. Empty vertex sets or empty families cannot satisfy the
non-two-colourability hypothesis. Edge size zero and one are excluded by the
original condition `r ≥ 2`.

The proof establishes the finite hypergraph statement. It does not encode a
separate infinitary compactness extension. It does not assert the optimal value
of the extremal function, nor the stronger classical numerical bound
`2^(r-1)/(4r)` mentioned in the background to the problem.

## Checks against weakened encodings

The final theorem assumes only uniformity and absence of a proper two-colouring.
No local lemma, probabilistic estimate, degree conclusion, existence of a
colouring, or external mathematical theorem is left as a hypothesis.
The core counting criterion is proved in this repository, not introduced as an
axiom. Rational-to-real conversion is itself checked in Lean.

`Sanity.lean` checks that the ordinary triangle is a valid two-uniform,
non-two-colourable input with all degrees two. It also proves that an individual
edge of size at least two is colourable. These checks exercise both sides of the
colouring definition.
