# Statement correspondence

## Original question and scope

The catalog asks whether a three-uniform, three-chromatic-critical hypergraph
can have minimum degree at least seven. The linked paper distinguishes
chromatic criticality from transversal criticality. This package answers the
catalog's **chromatic** question affirmatively. It makes no claim to formalize
the paper's separate negative theorem about transversal criticality.

Source: Ruiliang Li, *On an Erdos-Lovasz problem: 3-critical 3-graphs of minimum
degree 7*, [version 1](https://arxiv.org/html/2512.24850v1), Theorem 4.1,
Definition 2.1, and Appendix A.

## Representation and definitions

`Hypergraph n` is a list of triples of vertices in `Fin n`. `Uniform` requires
the entries of every triple to be strictly increasing. Thus each triple is the
canonical ordered representation of a three-element subset. `Simple` requires
the edge list to have no duplicates. Together these represent an ordinary
finite simple three-uniform hypergraph; list order has no mathematical role.

`Proper H c` says each edge's first vertex differs in colour from at least one
of its other two vertices. The theorem `proper_iff_nonmonochromatic` proves its
equivalence to the usual condition that every edge contains two vertices of
different colours. This is weak hypergraph colouring, not rainbow colouring.

`Colorable H k` quantifies over **all functions** `Fin n -> Fin k`; it is not
restricted to a sampled or externally generated list of colourings.
`coloring_complete` proves that the nine-parameter representation used in the
finite non-colourability certificate covers every such binary colouring.

`Degree H v` counts the edges incident with `v`, once per edge. `DeleteEdge`
removes the specified edge; `DeleteVertex` removes all incident edges. The
latter retains an isolated ambient vertex label, which cannot affect weak
colourability. `vertex_deletion_restricted` explicitly supplies a colouring
whose domain is the subtype of vertices other than the removed vertex.

## Checked conclusions

| Lean theorem | Mathematical conclusion |
| --- | --- |
| `uniform`, `simple` | Three distinct vertices per edge; no duplicate edges |
| `edge_count` | Exactly 22 edges on the ambient 9 vertices |
| `minimum_degree`, `degree_seven` | Every degree is at least 7, and one equals 7 |
| `not_two_colorable`, `three_colorable` | Not two-colourable; three-colourable |
| `no_fewer_colors` | No colouring with any number of colours below 3 |
| `edge_critical`, `vertex_critical` | Every single deletion is two-colourable |
| `deletion_chromatic_number_two` | Every deletion is also not one-colourable |
| `proper_subgraph_colorable` | Every strict edge subhypergraph is two-colourable |
| `jsp_000690` | Existence of a simple three-uniform, critically three-chromatic hypergraph with minimum degree at least 7 |

The paper's vertices 1 through 9 are represented by 0 through 8. All 22 edges
are transcribed with this uniform shift. The finite certificates are checked
by ordinary `decide`, whose proof terms are checked by the Lean kernel.
External Python calculations are not premises of any theorem.

## Review boundaries

This correspondence document is the submitter's explanation, not an authorized
curator's signed statement review. Independent reviewers should inspect the
definitions and compare the edge list with the source. The package does not
fabricate independent verification, recipient confirmation, historical
priority, or award eligibility.
