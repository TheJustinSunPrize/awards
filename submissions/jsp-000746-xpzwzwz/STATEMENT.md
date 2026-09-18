# Statement correspondence

Target: [JSP-000746](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000746),
corresponding to [Erdős #895](https://www.erdosproblems.com/895).

The question asks for an independent additive triple in every triangle-free
graph on a sufficiently large interval of integers. We prove the explicit
bound 18 recorded on the problem website.

| Mathematical condition | Lean expression |
| --- | --- |
| An arbitrary simple undirected graph | `G : SimpleGraph ℕ` |
| No triangle | `G.CliqueFree 3` |
| Positive first vertex | `0 < a` |
| Distinct, ordered summands | `a < b` |
| Third vertex is their actual sum | `a + b : ℕ` |
| All three vertices lie in `[1,18]` | positivity/order and `a + b ≤ 18` |
| Pairwise nonadjacency | `G.IsIndepSet {a,b,a+b}` |

Positivity implies `b < a+b`; thus all three vertices are distinct. Zero is
never used as a witness. There is no bound on the total number of vertices,
no assumption of a finite graph, and no additional assumption about edges outside the
first 18 positive integers beyond triangle-freeness.

The finite-interval corollary uses a graph on `Fin (n+1)` with `18 ≤ n`.
The unused zero vertex allows the positive vertices to be exactly `[1,n]`.
The conclusion compares natural-number values and states `c.val = a.val + b.val`,
so it has no finite-type arithmetic wraparound.

## Why the finite obstruction proves the general result

For each of the 153 unordered pairs in `[1,18]`, associate a proposition that
its endpoints are adjacent. Any three mutual adjacencies would form a clique
of size three, contradicting `CliqueFree 3`. If the desired triple did not
exist, every distinct positive Schur triple in `[1,18]` would contain an edge.
A subset of these two kinds of constraints is already contradictory.
Every input clause of the propositional proof is separately discharged by a
Lean theorem from those graph assumptions.

The finite bound is sufficient for the entire existence question, rather than
only checking one graph. The propositional proof quantifies over every edge
assignment. We do not claim a proof of the stronger infinite Hindman-set
question, or a new proof of the optimality of 18.
