# Statement correspondence

The source problem asks, among other things, whether an intersecting
r-uniform three-chromatic hypergraph must have two edges meeting in a number
of vertices bounded below by a universal positive constant times r.
Source: [Erdős 836](https://www.erdosproblems.com/836).

`JSP692.jsp000692_question_two` proves exactly this assertion for finite
hypergraphs with r >= 2, with constant C = 1/3. The stronger auxiliary theorem
`JSP692.large_intersection_nat` proves `r <= 2 * (e ∩ f).card + 1` from
non-two-colorability alone. Both require distinct witness edges explicitly.

- `Hypergraph V = Finset (Finset V)`: no repeated vertices in an edge and no
  repeated edges. `Uniform H r` requires every edge to have exactly r vertices.
- `Intersecting H` requires nonempty pairwise intersections.
- `Proper H c` requires two differently colored vertices in every edge,
  hence no monochromatic edge (weak coloring).
- `ThreeChromatic H` requires existence of a proper `Fin 3` coloring and
  nonexistence of a proper `Bool` coloring. A one-coloring would induce a
  Bool coloring, so this expresses exactly three colors.
- The final theorem quantifies over every rank r >= 2, every finite vertex
  count n, and every hypergraph on `Fin n`. Relabeling covers arbitrary finite
  vertex sets; the stronger lemmas directly use an arbitrary finite type V.
- The matrix bound is proved by finite double counting, not assumed.
  Existence of the extremal unique-edge vertex set, both witness families,
  and the intersection estimates are all proved in the dependency chain.
- The main theorem has no extra hypotheses asserting the desired bound.
  Isolated vertices do not affect its statement or proof.

This is submitter-produced statement review, not an independent endorsement.
Question 1, about the number of active vertices, is outside the theorem's scope.
