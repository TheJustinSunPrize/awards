# Independent statement and proof review

Review date: 2026-09-17.

This review was performed by a separate OpenAI Codex collaborating agent. It checks mathematical meanings, theorem statements, and proof arguments. It is not an external specialist review. The reviewing agent did not edit the Lean files and did not run an independent Lean kernel build. Build results and axiom reports belong to the project's verification records; source review does not replace those checks.

## Scope and conclusion

Reviewed modules: `Basic`, `Construction`, `TriangleWeight`, `WeightedPacking`, `Parity`, and `Bounds`, including `error_lower_bound_of_le` and `no_uniform_error`.

No mathematical weakening, vacuous hypothesis, quantifier error, or invalid use of truncated natural subtraction was found. The final necessary loss is `12*t^2 - 2*t`.

The result is a quantitative obstruction for the error term in Erdos problem 1009. It is not another proof of Gyori's affirmative solution or a claim to solve a new open problem.

## Graph and packing definitions

`Vertex r s` is the nested disjoint sum of `Fin r`, `Fin r`, and `Fin s`. It provides three disjoint classes A, B, C of sizes r, r, s. `part` labels these 0, 1, 2.

`graph` contains every cross-class edge and every edge inside C, with no loops and no edges inside A or B. Its adjacency expression is asymmetric in appearance, but the supplied symmetry proof is correct. It is exactly K_{r,r,s} with a complete graph on C.

`IsPacking G P` requires each member to satisfy Mathlib's `IsNClique 3`, including both pairwise adjacency and cardinality exactly three. The members are genuine triangles with different vertices.

`arcs T = T.offDiag` contains both orientations of every triangle edge. Disjointness of these sets forbids a shared undirected edge, including an edge written in reverse order. It allows sharing one vertex, as an edge-disjoint packing should. Repeated copies of a triangle would share edges, so representing the family as a finite set loses no legitimate packing.

## Basic weighted argument

The oriented-edge weight is 2 inside C, 3 between C and the other classes, and 0 otherwise. It is symmetric. The nonedges inside A and B have weight zero, so summing over all distinct ordered pairs adds no fictitious positive resources.

The possible triangle types ABC, ACC, BCC, CCC have total oriented weights 12, 16, 16, 12 respectively. Every triangle therefore consumes at least 12 units. The total available weight is

`12*r*s + 2*s*(s-1)`.

Pairwise disjointness allows `sum_biUnion` to count each used oriented edge exactly once. The generic resource argument gives

`6*P.card <= 6*r*s + s*(s-1)`.

This applies to every packing and does not assume maximality or maximum cardinality. The graph's vertex, degree, and edge-count formulas agree with the construction. Zero-size cores are handled separately wherever natural subtraction requires it.

## Parity module

`coveredNeighbors P v` is the union of `T.erase v` over packing members containing v. Its membership equivalence with `(v,w)` belonging to the union of packing arcs is exact: erasure removes loops and the filter supplies membership of the first endpoint.

For two different triangles containing v, their erased sets are disjoint. A common w would otherwise produce the common oriented edge `(v,w)`. Every erased set has two elements, and `card_biUnion` therefore proves

`(coveredNeighbors P v).card = 2 * (P.filter (fun T => v in T)).card`.

Thus the covered degree is even. This argument is valid for any simple graph and needs no maximality hypothesis.

For a core vertex, every other vertex is adjacent. With s even, its full neighbor count `2*r+s-1` is odd. The input `c : Fin s` supplies positivity of s. The covered neighbor set is contained in `univ.erase v`; even and odd cardinalities cannot be equal. A strict cardinality inequality therefore supplies an unused outgoing arc.

One such arc is selected from each core vertex. The map into ordered pairs is injective because its first coordinate identifies that vertex, so the selected set M has cardinality s. Every selected arc is non-diagonal, is absent from the union U of packing arcs, and has weight at least 2. The disjoint union of U and M is contained in all non-diagonal ordered pairs. Consequently

`12*P.card + 2*s <= 12*r*s + 2*s*(s-1)`.

Selecting arcs with the same terminal vertex causes no problem. Selecting opposite orientations of one unused undirected edge is also legitimate: both orientations occur in the total resource.

The weighted statement handles s=0 using an empty selected family. The subsequent `bound_even_core` explicitly requires s>0 and Even s, which implies s>=2 before rewriting subtraction. Its conclusion is

`6*P.card <= 6*r*s + s*(s-2)`.

No assertion about the actual maximum packing or equality attainment is used.

## Final parameters and subtraction

Set s=12t with t>0. The reviewed statements give

- n = 2r+12t;
- m = r^2+24rt+72t^2-6t;
- k = m-floor(n^2/4) = 12tr+36t^2-6t.

The order n is even. The natural-number expression `n^2/4` is exactly `(r+6*t)^2`, hence matches the floor in the source problem.

The parity bound gives `P.card+4*t <= 12*t*r+24*t^2`, and therefore

`P.card + (12*t^2-2*t) <= excess r t`.

`excess_add` and `loss_add` add back the subtracted terms under t>0. Their proofs ensure the minuends are sufficiently large. No result relies on a false identity for truncated subtraction.

The strict parameter condition is retained: `6*t*n-k = 36*t^2+6*t > 0`. Thus k<c*n holds with c=6t, not merely k<=c*n.

## Unbounded graph orders and eventual bounds

For each fixed positive t and every order threshold N, `arbitrarily_large_obstructions` selects r=N. The resulting graph has at least N vertices, its edge count is exact, it satisfies the strict excess condition, and every legitimate packing satisfies the asserted upper bound. The parameter c=6t stays fixed while graph order is unbounded.

`IsEventualErrorBound c f` permits an order threshold N and then quantifies over every finite vertex type, every graph, and every natural k meeting the edge-count and strict linear conditions. It is weaker than a guarantee applying at every order. A necessary lower bound for this eventual version also applies to the original version.

The finite and decidability instances provide the structures needed to express finite sums and edge sets; they do not exclude the explicit witness graph. Every antecedent is supplied by the construction theorems.

The guarantee yields a packing P with `k <= P.card+f`. The construction applies to that same P and gives `P.card+loss <= k`. Combining and cancelling proves `loss <= f`. There is no switch of packing between the two inequalities.

## Parameter transfer and uniform errors

`IsEventualErrorBound.mono_parameter` has the correct direction: a guarantee valid at c also holds at d<=c, since k<d*n implies k<c*n for nonnegative order n.

Accordingly, `error_lower_bound_of_le` establishes this precise extension:

For every positive natural t and every real c>=6t, any natural f satisfying `IsEventualErrorBound c f` obeys `12*t^2-2*t <= f`.

`no_uniform_error` correctly rules out a single natural f that works for every positive real c. It takes t=f+1, whose necessary lower bound exceeds f. The allowed graph-order threshold may depend on c; the unbounded-order obstruction still defeats it.

No separately named real asymptotic statement or closed expression using floor(c/6) is implemented. The parameter-transfer theorem itself supports the exact displayed bound for every c>=6t.

## Attribution and scope limits

The proof bounds packing size from above in the witness family and obtains a necessary loss. It does not construct a packing attaining that bound and does not claim an exact maximum-packing formula.

Sauer's four-vertex-core construction and Gyori's affirmative result are prior mathematics. The accurate description is an incremental formalization of a construction family and its quantitative loss, including an explicit parity argument. Build success alone establishes neither global priority, new mathematical discovery, nor award eligibility.
