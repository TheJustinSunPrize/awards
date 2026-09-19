# Mathematical argument

Let B be a set of natural numbers. Define E_B(N) as the number of integers in {1,...,N} that do not belong to B. Suppose B has the following property:

> If x < y are adjacent members of B (no member of B lies strictly between them), then xy does not belong to B.

This is weaker than distinctness of all nonempty consecutive block products.

## Finite counting theorem

For natural numbers N, m and t satisfying

\[
m^2\le N,\qquad m<(t+1)^2,
\]

we prove

\[
m\le E_B(N)+t+1.
\]

Let S = B intersect (t,m], and list its k members as b_1 < ... < b_k. Let L be the set of missing positive integers up to m. Every integer in {1,...,m} belongs to {1,...,t}, S, or L. Therefore

\[
m\le t+k+|L|.
\]

If k = 0 the required inequality follows immediately, since L is a subset of the missing integers up to N (m <= m^2 <= N).

If k >= 1, consider the k-1 products b_i b_(i+1). Two consecutive members of S are adjacent in B: any intervening member of B would also lie in (t,m] and hence in S. Thus every product is absent from B. Further,

\[
m<(t+1)^2\le b_i b_{i+1}\le m^2\le N.
\]

The products are strictly increasing, so there are exactly k-1 distinct missing values above m. They are disjoint from L, giving

\[
E_B(N)\ge |L|+k-1\ge m-t-1.
\]

This argument counts actual missing integers; it never assumes different forcing conditions choose different omissions unless injectivity and disjointness have been established.

## Square-root consequence

Take m = floor(sqrt(N)) and t = floor(sqrt(m)). The hypotheses hold at every natural N, including zero. This gives the displayed bound in README. Since m >= sqrt(N)-1 and t <= N^(1/4), it also gives

\[
E_B(N)\ge\sqrt N-N^{1/4}-2.
\]

There is no density hypothesis in either step. The real-valued displayed inequality and the limiting-language conclusion are elementary interpretations of the checked integer statement; the Lean file avoids a separate real-analysis limit formalization.

Instead, the Lean file also proves a fully quantified integer version of the asymptotic coefficient: for every integer k >= 1 and every N >= (2k)^4,

\[
(k-1)\lfloor\sqrt N\rfloor\le kE_B(N).
\]

Indeed, then t >= 2k, so k(t+1) <= t^2 <= m. Multiplying m <= E_B(N)+t+1 by k and using this inequality gives the claim. Taking arbitrarily large k and using floor(sqrt(N))/sqrt(N) -> 1 yields the stated limiting coefficient.

## Bridge to the original sequence problem

Let a be a strictly increasing sequence indexed by the natural numbers. Suppose products on all nonempty finite index intervals are distinct. Put B = range(a).

If a_i < a_j are adjacent members of B, strict increase and absence of an intervening member imply j=i+1. If a_i a_(i+1) = a_k for some k, then the block [i,i+1] has the same product as [k,k]. Block-product injectivity would imply both i=k and i+1=k, a contradiction. Thus B has the adjacency property, and the finite theorem applies.

All these implications, including the k=0 counting boundary and the sequence bridge, appear in the Lean proof. The theorem applies without needing a density-one assumption; in particular it applies to the density-one sequences considered in the original existence problem.
