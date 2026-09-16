# Direct weighted light-edge argument

Let G be a finite simple graph, m its edge count, z(v) nonnegative integral
weights, Z their sum, and D(v)=deg(v)+z(v). Assume m>=6 and no single vertex
meets every edge. If m+Z<=8, some edge uv has D(u)+D(v)<=6. If m+Z<=9,
some edge uv has D(u)+D(v)<=7.

Write b=6 or 7 for the respective desired bound. If D(w)>=5, choose an edge
uv avoiding w. For three distinct vertices, deg(u)+deg(v)+deg(w)<=m+3:
each edge is counted once, except the at most three edges inside the triple
which can contribute one extra. The weight sum on the triple is at most Z.
Consequently D(u)+D(v)<=m+Z+3-D(w)<=b.

Otherwise every D is at most four. Suppose all edges have endpoint sum >b.

For b=7, both endpoints of every edge must have D=4. With h such vertices,
4h<=2m+Z and m<=h(h-1)/2. Since m+Z<=9, h<=4. If h<=3 the edge bound
contradicts m>=6. If h=4, the weighted sum gives m>=7 while the edge bound
gives m<=6, again a contradiction.

For b=6, every edge has endpoint types (4,4), (4,3), or (3,4). Let h,l
count the vertices of the two types. The D=4 vertices form a cover, so h>=2
by the hypothesis excluding a one-vertex cover. We have
4h+3l<=2m+Z, m<=h(h-1)/2+h*l, and m+Z<=8. These imply h<=4.
If h=4, then l=0, m=8, and m<=6, impossible.
If h=3, then l<=1; l=0 contradicts m>=6, and l=1 gives m>=7 and m<=6.
If h=2, m>=6 forces l>=3, whereas 8+3l<=2m+Z<=16 forces l<=2.

For a seven-vertex graph with independence number at most five, a one-vertex
cover is impossible: the other six vertices would be independent. This gives
both exact seven-vertex statements used in the r=7 roadmap. No enumeration
or computational axiom is used in the Lean proof.

The complete K50 seven-color theorem uses this lemma through
`JSP500/WeightedCoverBridge.lean`. See [the full proof outline](PROOF.md).
