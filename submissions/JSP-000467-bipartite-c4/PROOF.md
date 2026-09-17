# Mathematical proof and scope

Let A and B be disjoint finite sets with sizes a and b. The complete bipartite
graph joins precisely those pairs with one endpoint in each class.

Every four-cycle alternates between A and B, so it has exactly two vertices in
each class. This remains true for either orientation and every choice of starting
vertex. If k such cycles are pairwise vertex-disjoint, their left vertices give
2k different elements of A, and their right vertices give 2k different elements
of B. Consequently

\[
k\le\min(\lfloor a/2\rfloor,\lfloor b/2\rfloor).
\]

Conversely, whenever 2k<=a and 2k<=b, label the vertices on each side by consecutive
integers. For each i in {0,...,k-1}, take the cyclic tuple

\[
(A_{2i},B_{2i},A_{2i+1},B_{2i+1}).
\]

Every consecutive pair, including the closing pair, is an edge. The four vertices
are different, and different values of i use disjoint pairs on both sides. This
constructs k disjoint C4 copies and proves the exact formula, including k=0.

The Lean definition uses one injection from `Fin k x Fin 4` into the vertex type
and requires adjacency at cyclically consecutive second indices. The module
`Basic` converts each member into Mathlib's `(cycleGraph 4).Copy G` and proves
that distinct members have disjoint vertex ranges. The upper bound therefore
applies to every genuine packing, not just the displayed construction.

For Wang's threshold, set a=2k-1 and b=2k+1, with k>0. There are 4k vertices.
Every left vertex has degree b and every right vertex has degree a, so the minimum
degree is 2k-1. The exact packing formula gives

\[
\min(\lfloor(2k-1)/2\rfloor,\lfloor(2k+1)/2\rfloor)=k-1.
\]

There is a packing of k-1 cycles but no packing of k cycles. In a graph of order
4k, a packing of k four-cycles would use every vertex, so this is exactly the
failure of a C4 factor. Taking k arbitrarily large gives an unbounded family.

If a proposed universal degree threshold d on graphs of order 4k were smaller
than 2k, this same graph would satisfy its hypothesis but fail its conclusion.
Thus d>=2k is necessary. Combining this necessity with Wang's prior positive
theorem establishes sharpness; the present source proves only the necessity and
the exact complete-bipartite packing formula.

Natural division in Lean is floor division. The positive-k hypothesis is used
before simplifying `2*k-1` and `k-1`, so the sharpness theorem does not mistake
truncated subtraction at k=0 for the intended graph order. The exact capacity
theorem itself has no positivity restrictions on a, b, or k.
