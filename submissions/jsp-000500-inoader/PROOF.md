# Proof of the fixed r=7 theorem

Assume a balanced seven-coloring on fifty vertices: every eight-vertex set
contains all seven colors. A color graph G has independence number at most
seven, and at most 22 edges on any eight vertices (the other six colors must
occupy at least one of the 28 available edges each). Some color has at most
175 edges, since 50 choose 2 = 1225. Brooks' theorem supplies a vertex of degree
at most six in this least color. Choose a vertex of minimum degree d.

## Colored core bounds

The KP saving inequality and the colored terminal obstruction give the
following excluded orders for a color graph with no seven-clique:

| Independence number at most | Excluded order |
| --- | --- |
| 2 | 14 |
| 3 | 22 |
| 4 | 30 |
| 5 | 40 |

These results carry the actual balanced-coloring hypothesis and are proved in
[CoreLadder.lean](JSP500/CoreLadder.lean), building on
[ColoredTerminal.lean](JSP500/ColoredTerminal.lean) and
[ExtremalBounds.lean](JSP500/ExtremalBounds.lean).

## Neighborhood counting

Write W for a vertex's nonneighbors and N for its neighbors. Minimum-degree
accounting gives the ordinary star inequality

`e(G) >= e(G[W]) + choose(d+1, 2)`.

Stronger local counts use the graph M complementary to G[N] and the
nonnegative weight `z(v) = cross_degree(v,W) - degree_M(v)`. The exact identity is

`e(G) = e(G[W]) + d + choose(d,2) + e(M) + sum z`.

See [GraphAccounting.lean](JSP500/GraphAccounting.lean) and
[NeighborhoodWeights.lean](JSP500/NeighborhoodWeights.lean).
For seven neighbors, the local 22-edge cap forces `e(M) >= 6`.
A nonadjacent pair must cover all but at most thirteen vertices of W, or the
colored core obstruction would extend to a forbidden independent set.
[PairCover.lean](JSP500/PairCover.lean) proves this extension and cover count.

The [weighted light-edge lemma](WEIGHTED_PROOF.md) is proved by direct counting
for arbitrary finite graphs. If M has no single-vertex edge cover and at least
six edges, then `e(M)+sum z <= 8` forces an edge of weighted endpoint degree
sum at most six, and budget nine forces one at most seven. Combining this
with pair coverage yields the two key fourth-level floors.

## Edge floors with no seven-clique

In the following table, a is the independence cap, n the vertex count, and b
the proved lower bound on the edge count. Each bound concerns a color graph
of a balanced coloring with no seven-clique.

| a | n | b |
| --- | --- | --- |
| 2 | 13 | 41 |
| 3 | 20 | 63 |
| 3 | 21 | 75 |
| 4 | 28 | 100 |
| 4 | 29 | 113 |
| 5 | 35 | 122 |
| 5 | 36 | 134 |
| 5 | 37 | 147 |
| 5 | 38 | 152 |
| 5 | 39 | 176 |
| 6 | 43 | 156 |

The proofs are in [FloorInfrastructure.lean](JSP500/FloorInfrastructure.lean),
[DirectFloors.lean](JSP500/DirectFloors.lean), and
[FinalFloors.lean](JSP500/FinalFloors.lean), with the weighted bridge in
[WeightedCoverBridge.lean](JSP500/WeightedCoverBridge.lean).
The KP equality classification and numerical recurrence programs are not used.

## Removing the clique restriction

An outside vertex has at most one neighbor in a monochromatic seven-clique,
by the 22-edge cap. Any set of at most six outside vertices therefore leaves
a clique vertex avoiding the set. Deleting the seven-clique lowers the
independence cap by one and removes at least 21 edges.

This first yields unconditional excluded orders 8, 15, and 22 at independence
caps 1, 2, and 3. At cap 4 on 29 vertices, a seven-clique would leave an
impossible cap-3 graph on 22 vertices, so the bound 113 is unconditional.
At cap 5 on 36 vertices, clique deletion gives at least 113+21 = 134 edges.
At cap 6 on 43 vertices, it gives at least 134+21 = 155 edges; if there is no
seven-clique, the stronger previously proved 156-edge bound applies.
See [CliquePeeling.lean](JSP500/CliquePeeling.lean).

## Vertex deletion and final contradiction

Vertex deletion preserves the balanced-coloring property and independence
cap. Summing `e(G-v) + degree(v) = e(G)` over all vertices lifts the
unconditional cap-6 floor to the following orders:

| Vertex count | Minimum edges |
| --- | --- |
| 43 | 155 |
| 44 | 163 |
| 45 | 171 |
| 46 | 179 |
| 47 | 187 |
| 48 | 196 |
| 49 | 205 |

These are [UnrestrictedFloors.lean](JSP500/UnrestrictedFloors.lean).
For the minimum-degree vertex x in the least color on fifty vertices,
its nonneighbors number 49-d and have independence cap six. The ordinary
star inequality now contradicts `e(G) <= 175` in every possible case:

| d | Nonneighbor floor | Star contribution | Forced e(G) |
| --- | --- | --- | --- |
| 0 | 205 | 0 | 205 |
| 1 | 196 | 1 | 197 |
| 2 | 187 | 3 | 190 |
| 3 | 179 | 6 | 185 |
| 4 | 171 | 10 | 181 |
| 5 | 163 | 15 | 178 |
| 6 | 155 | 21 | 176 |

This discharges the balanced-coloring assumption in
[Main.lean](JSP500/Main.lean). Negating it produces the required eight-set and
missing color, proving both final declarations.
