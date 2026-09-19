# Mathematical proof and statement correspondence

For every n>=2, let m(n) be the least number of edges of a finite simple n-uniform hypergraph of weak chromatic number exactly three. The delivered theorem proves `0 < m(n) <= 4*n^2*2^n`. It does not settle the precise-growth problem or improve the classical upper bound.

## Candidate edges and finite counting

Put N=2*n^2, E=choose(N,n), D=choose(n^2,n). Every binary partition of N vertices has a part of at least n^2 vertices, giving at least D monochromatic candidate edges. For i=0,...,n-1, put x_i=i/n^2. The proved finite product inequality `product(1-x_i)>=1-sum(x_i)>=1/2` gives `(n^2)^n <= 2*(n^2 falling-factorial n)`. Combining this with `(N falling-factorial n)<=N^n` and cancelling the common positive factor n! yields `E<=2^(n+1)*D`.

Set a=2^(n+1) and M=N*a=4*n^2*2^n. If every M-tuple of candidate edges failed at some binary partition, choosing a failing partition would inject all E^M tuples into a dependent sum of 2^N bad-tuple spaces, each of size at most (E-D)^M. But q=1-D/E is nonnegative, q^a<=exp(-1), and 2<exp(1). Thus `(2*q^a)^N<1`, equivalently `2^N*(E-D)^M<E^M`, a contradiction. The exponential inequalities are proved using Mathlib theorems, not floating-point approximations. The whole choice/counting argument is formalized over finite types and requires no external random experiment or solver oracle.

## Simple hypergraph and exact three colours

Take the finite image of a hitting tuple to remove duplicate edges; the resulting family has at most M distinct n-element edges and cannot be two-coloured. Select an inclusion-minimal non-two-colourable edge subfamily. Delete an edge e and two-colour the rest, then give one vertex u of e a new third colour. Every edge containing u has another vertex because n>=2, and is not monochromatic. Edges not containing u differ from e and retain their proper old colouring. Consequently the subfamily has weak chromatic number exactly three. An enlargement of palettes rules out zero/one colour as well.

Minimality is proved for every proper edge subfamily. Vertex-criticality is not asserted; the chosen ground set may contain isolated vertices. Edges are ordinary `Finset`s, and the edge family is also a `Finset`, so repeated vertices or duplicate edges cannot be counted as distinct. Colourings are actual functions into `Fin k`.

## Extremal function and explicit endpoint

`Attainable n k` ranges over all finite ground-set sizes `Fin N`. The construction establishes nonemptiness. `m_attained` proves the natural infimum is an actual attained edge count, not the default infimum of an empty set. Empty edge families are two-colourable; hence `m_positive`. The constructed family yields `m_upper_bound`.

`StatementCheck.lean` separately exposes an endpoint using explicit finite sets and plain quantifiers: for every n>=2, a family on 2*n^2 vertices, each edge of size n, at most 4*n^2*2^n edges, a proper three-colouring, and a monochromatic edge under every two-colouring. Its accompanying examples verify the semantics on a genuine two-vertex edge and an impossible singleton edge. This adapter is contributor-written, not independent human certification.

Mathematical attribution remains with Erdos (1964) and the cited literature in README.md. The formalization concerns only this known all-parameter upper-bound component; the full original estimate problem, sharper constants, exact small values and improved lower bounds are outside the package.
