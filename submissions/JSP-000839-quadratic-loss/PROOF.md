# A quadratic loss obstruction for Erdős problem 1009

This project formalizes a family of lower-bound examples for [Erdős problem 1009](https://www.erdosproblems.com/1009), corresponding to JSP-000839 in the Justin Sun Prize catalog. The principal statement established here is

\[
f(6t)\ge 12t^2-2t\qquad(t\in\mathbb N,\ t>0),
\]

for any nonnegative integer error bound satisfying the triangle-packing guarantee in that problem. The conclusion remains valid if the guarantee is required only above a threshold in the number of vertices.

## Attribution and scope

Erdős problem 1009 is already solved. Győri proved the existence of an error term of order \(O(c^2)\); this project does not supply a new solution of that upper-bound problem. The [problem record](https://www.erdosproblems.com/1009) gives the reference E. Győri, *On the number of edge-disjoint triangles in graphs of given size* (1988), pp. 267–276.

The same record attributes to Sauer the graph obtained by adding a complete graph on the four-vertex class of \(K_{r,r,4}\). Its stated purpose is to show that an error term of zero cannot always hold: the graph has \(n=2r+4\) vertices and \(\lfloor n^2/4\rfloor+2n-6\) edges, but at most \(2n-7\) edge-disjoint triangles. The graph family used below replaces that four-vertex core by a core of arbitrary size \(s\). The construction's mathematical novelty has not been established, and no novelty claim is made for this parameter extension.

A [public Lean formalization of the main upper-bound result](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1009.lean) already exists. The source in this project was written anew to formalize the lower-bound family and its consequence for an eventual error bound. This project makes no claim to the first formalization worldwide and no claim to an award entitlement.

The bound proved here is an upper bound on the number of triangles in any packing in the constructed graphs. We do not prove that a packing attains that bound, determine their exact maximum packing size, or determine the optimal error function for problem 1009.

## 1. The original guarantee and its eventual version

For each real \(c>0\), the original problem asks for an error \(f(c)\), depending only on \(c\), such that every \(n\)-vertex graph with at least

\[
\left\lfloor\frac{n^2}{4}\right\rfloor+k
\]

edges, where \(k<cn\), has at least \(k-f(c)\) pairwise edge-disjoint triangles.

The formal definition `IsEventualErrorBound c f` permits a threshold \(N\): for every finite simple graph of order \(n\ge N\) and every natural number \(k\) satisfying those two edge and parameter conditions, there must be a packing \(P\) with

\[
k\le |P|+f.
\]

This form avoids subtraction of natural numbers. A bound valid for every \(n\) is a special case, with threshold zero. Proving a necessary lower bound under the weaker eventual guarantee also proves it for the original guarantee.

## 2. The graph family and its counts

Let \(A,B,C\) be disjoint sets with

\[
|A|=|B|=r,\qquad |C|=s,\qquad r,s\in\mathbb N.
\]

Define \(G_{r,s}\) by making \(A\) and \(B\) independent and placing an edge between every other pair of distinct vertices. Thus \(G_{r,s}\) is \(K_{r,r,s}\) with all the edges of a complete graph added inside \(C\).

In Lean, its vertex type is

```lean
Vertex r s := (Fin r ⊕ Fin r) ⊕ Fin s
```

and `part` assigns the three classes the labels \(0,1,2\). The graph adjacency relation requires distinct endpoints and either different class labels or both endpoints in the core.

Its order and edge count are

\[
n=2r+s,\qquad m=r^2+2rs+\frac{s(s-1)}2.
\]

The degree of each vertex in \(A\) or \(B\) is \(r+s\), and the degree of each core vertex is \(2r+s-1\). `edge_card_twice` uses the degree-sum identity and records the division-free formula

\[
2m=2r^2+4rs+s(s-1).
\]

These counts include the cases \(r=0\) and \(s=0\).

## 3. Weighted counting of a triangle packing

For a finite vertex set \(T\), `arcs T` is its set of ordered pairs of distinct vertices. In particular, the arcs of a triangle are its six oriented edges. A packing is a finite set of three-vertex cliques whose arc sets are pairwise disjoint. For triangles in a simple graph, this is exactly the usual condition that no undirected edge belongs to two different triangles; sharing a vertex is permitted.

Give each ordered pair of distinct vertices the following nonnegative integer weight:

| Position of the endpoints | Weight |
| --- | ---: |
| Exactly one endpoint is in \(C\) | 3 |
| Both endpoints are in \(C\) | 2 |
| Neither endpoint is in \(C\) | 0 |

The definition is available on all ordered pairs, but sums over `offDiag` exclude loops. Including all distinct ordered pairs in the ambient sum is harmless: nonedges inside \(A\) or \(B\) have weight zero.

Every triangle has at least one core vertex, since the graph outside the core is bipartite. Its possible types and weights are:

| Triangle type | Sum of its six arc weights |
| --- | ---: |
| One vertex in each of \(A,B,C\) | \(4\cdot3+2\cdot0=12\) |
| Two core vertices and one outside vertex | \(4\cdot3+2\cdot2=16\) |
| Three core vertices | \(6\cdot2=12\) |

Thus `triangle_weight` proves that every triangle has weight at least 12.

There are \(4rs\) oriented pairs joining the core to its complement and \(s(s-1)\) oriented pairs internal to the core. Consequently `total_weight` proves

\[
W=12rs+2s(s-1).
\]

Pairwise edge-disjointness means that no arc is counted twice across the packing. The generic theorem `IsPacking.weighted_bound` therefore gives

\[
12|P|\le W=12rs+2s(s-1).
\]

Dividing by two yields `packing_bound`:

\[
6|P|\le6rs+s(s-1).
\tag{1}
\]

The argument applies to every packing. It does not assume that the packing is maximal or maximum.

## 3a. The improvement for an even core

When `s` is even, each core vertex has odd degree `2*r+s-1`. In a packing,
each triangle containing a vertex uses exactly two of its incident edges.
Since different triangles share no edge, the covered neighbor count at each
vertex is even. Hence each core vertex has an unused neighbor.

For every core vertex, choose one unused oriented edge starting at that
vertex. These `s` oriented edges are distinct because their sources are
distinct. Each has weight at least 2, and none is used by the packing.
Consequently the unused oriented weight is at least `2*s`, giving

\[
12|P|+2s\le12rs+2s(s-1).
\]

For positive even `s`, `IsPacking.bound_even_core` therefore proves

\[
6|P|\le6rs+s(s-2). \tag{1a}
\]

The two selected edges for different vertices may be opposite orientations
of the same edge; this is valid because the resource throughout is a set of
oriented edges. The proof never assumes that the selected undirected edges
are distinct.

## 4. Choosing an integral parameter family

Take a positive integer \(t\) and put \(s=12t\). The number of vertices is even, and

\[
\begin{aligned}
n&=2r+12t,\\
m&=r^2+24rt+72t^2-6t,\\
\left\lfloor\frac{n^2}{4}\right\rfloor&=(r+6t)^2.
\end{aligned}
\]

Define

\[
k=12rt+36t^2-6t,\qquad d=12t^2-2t.
\]

Both are nonnegative integers for \(t>0\). Lean uses the definitions `excess r t` and `loss t`, together with the subtraction-free identities

\[
k+6t=12rt+36t^2,\qquad d+2t=12t^2.
\]

The edge count is exactly

\[
m=\left\lfloor\frac{n^2}{4}\right\rfloor+k.
\]

At the original problem's parameter \(c=6t\), the required strict inequality follows from

\[
cn-k=36t^2+6t>0.
\]

Specializing the strengthened inequality (1a) gives

\[
|P|+4t\le12rt+24t^2.
\]

Subtracting this inequality from the expression for \(k\), or equivalently combining the subtraction-free identities above, gives `packing_loss`:

\[
|P|+d\le k,\qquad d=12t^2-2t.
\tag{2}
\]

This holds for every \(r\ge0\) and every edge-disjoint triangle packing in \(G_{r,12t}\).

## 5. Arbitrarily large examples and the lower bound on the error

Fix \(t>0\). Given any order threshold \(N\), choose \(r=N\); then \(n=2r+12t\ge N\). `arbitrarily_large_obstructions` packages this order bound, the exact edge count, the strict condition \(k<6tn\), and (2).

Suppose `IsEventualErrorBound (6 * t) f` holds. Choose one of these graphs beyond the threshold supplied by that assertion. Its guaranteed packing would satisfy

\[
k\le |P|+f,
\]

whereas every packing satisfies \(|P|+d\le k\). Combining the two gives \(d\le f\). This is `error_lower_bound`:

\[
f\ge12t^2-2t.
\]

Thus a bound valid for all positive real parameters cannot have a uniform constant error or a globally linear error in \(c\). Along \(c=6t\), the necessary error is at least \(c^2/3-c/3\). These are mathematical consequences of the displayed formal lower bound; the project does not claim that the coefficient \(1/3\) is optimal.

## 6. Theorem map

All declarations below are in the namespace `TrianglePacking`.

| Source module and declaration | Scope |
| --- | --- |
| `Construction.vertex_card` | Order \(2r+s\), for all natural \(r,s\). |
| `Construction.degree_left`, `degree_right`, `degree_core` | Degrees of the three vertex classes, when the chosen vertex exists. |
| `Construction.edge_card_twice` | Exact general edge count, expressed after multiplication by two. |
| `Construction.edge_card_twelve` | Exact edge count for \(s=12t\), expressed as \(m+6t=r^2+24rt+72t^2\). |
| `Construction.total_weight` | Exact weight of all distinct ordered pairs. |
| `TriangleWeight.sum_arcs_triple` | Six-arc expansion for three distinct vertices and any natural-valued weight. |
| `TriangleWeight.triangle_weight` | Weight at least 12 for each three-clique of \(G_{r,s}\). |
| `WeightedPacking.sum_arcs_le_sum_offDiag` | Weight of pairwise disjoint arc sets is bounded by all available arcs. |
| `WeightedPacking.weighted_bound_of_pairwise` | Converts a per-member lower weight into a cardinality bound. |
| `WeightedPacking.IsPacking.weighted_bound` | The same generic estimate applied to a graph packing. |
| `Parity.IsPacking.card_coveredNeighbors` | Exact even covered neighbor count. |
| `Parity.IsPacking.exists_unused_core_arc` | An unused outgoing edge at every core vertex when the core is even. |
| `Parity.IsPacking.bound_even_core` | Strengthened inequality (1a) for all positive even core sizes. |
| `Bounds.packing_bound` | Inequality (1) for arbitrary \(r,s\). |
| `Bounds.packing_twelve` | Specialized packing bound for \(s=12t\), \(t>0\). |
| `Bounds.excess_add`, `loss_add` | Arithmetic identities justifying natural-number subtraction. |
| `Bounds.packing_loss` | Inequality (2), for every packing in the chosen family. |
| `Bounds.balanced_threshold` | Exact value of \(\lfloor n^2/4\rfloor\). |
| `Bounds.edge_count_excess` | Exact edge count equals threshold plus `excess`. |
| `Bounds.excess_lt_parameter` | The strict original condition \(k<6tn\). |
| `Bounds.arbitrarily_large_obstructions` | Obstruction graphs beyond every order threshold. |
| `Bounds.IsEventualErrorBound` | The quantified eventual guarantee being tested. |
| `Bounds.error_lower_bound` | Any such error at \(c=6t\) is at least \(12t^2-2t\). |

The module prefixes in the table identify files, not additional Lean namespaces. For example, the last theorem's full Lean name is `TrianglePacking.error_lower_bound`.

## 7. Verification and parameter transfer

The final source includes the parity refinement described above. The theorem
`error_lower_bound_of_le` applies the same necessary loss to every real
parameter `c >= 6*t` by monotonicity of the guarantee. `no_uniform_error`
formally proves that no constant error works for all positive real parameters.
Build, axiom-audit and local kernel-replay evidence are recorded separately in
`verification/`; those logs describe the exact submitted source revision and
its trust boundary.
