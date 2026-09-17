# Scope and statement correspondence

**Partial Progress: finite upper bounds for the single (5,3) prohibition and the combined (5,3)/(6,4) prohibitions.**

`TripleOn V` is a finite vertex subset of cardinality three. `TripleSystemOn V` is a finite set of such triples. Thus vertices within an edge and edges within the hypergraph are distinct; this is not a multihypergraph.

`FkFree 5 G` means that every subfamily `C` of `G` with exactly three edges has a vertex union of cardinality greater than five. It is a non-induced prohibition: the presence of additional edges never rescues a forbidden three-edge subfamily. There is no extra `FkFree 4`, linearity or codegree hypothesis.

The first terminal theorem quantifies over **all natural numbers `n`** and **all `G : TripleSystem n`**, with only that freeness hypothesis. The conclusion is the finite integer inequality

`5 * G.card <= 2 * n.choose 2`.

The second terminal theorem quantifies over all `n` and bounds `extremalNumber 5 n`, which is explicitly defined as the finite maximum of the cardinalities of all free edge families. It is not an assumed extremal oracle. Its proof takes the finite supremum of the first theorem.

## Small orders and the original forbidden-family language

The formal model prohibits three edges spanning **at most five** vertices. For ambient order `n >= 5`, this is equivalent to finding a forbidden three-edge family on exactly five vertices, since isolated vertices can be added. For `n < 5`, this equivalence is not asserted: an exactly-five-vertex search would be empty, while the present at-most-five condition remains meaningful. For example, the complete three-uniform hypergraph on four vertices violates the present freeness assumption.

No extra hypothesis is introduced merely to avoid small orders. The all-`n` bound is proved in the explicit at-most-five model, including the empty vertex and edge cases.

## Proof invariant and actual contribution

The stronger target `Erdos1076Upper.five_mul_card_le_two_shadow` proves

`5 * G.card <= 2 * (pairShadow G).card`.

The structural argument is proved from freeness, rather than assumed: if two distinct triples share a pair, they span four vertices, use five distinct pairs, and no third edge can contain any pair from those four vertices. Otherwise those three edges would span at most five vertices. This makes the one-edge or two-edge deletion argument valid. The finite shadow bound and the extremal supremum are connected to complete terminal theorems.

This scope differs from the cumulative high-girth family used in PR90, whose upper bound uses the additional `FkFree 4` condition. It also differs from the pinned plby source's cofinal `92/529` lower construction. Only the six minimal definitions are reproduced here; the new upper-bound argument does not depend on that lower construction.

## Combined F5-and-F6 increment

`FkFree 6 G` prohibits every four-edge subfamily spanning at most six vertices. Together with `FkFree 5 G`, and without `FkFree 4`, it implies `3 * G.card <= n.choose 2` for every natural `n`. The contrapositive says that exceeding the pair budget forces failure of at least one of these two freeness conditions.

The existing `extremalNumber k n` filters a single Fk condition. No claim is made that the combined bound applies to `extremalNumber 5 n` or `extremalNumber 6 n`, and no new combined-family extremal definition is introduced. The graph theorem itself is the submitted finite upper contribution. The exact-five/exact-six ambient wording agrees with both at-most conditions when `n >= 6`; the all-n formal statements retain explicit at-most semantics.

The completed pair shadow contains ordinary edge pairs and every pair on the four-vertex union of two distinct edges sharing a pair. No freeness assumption enters that definition. The additional sixth pair is unused under F5-freeness. When deleting two edges, F6 is applied only after proving all four edges of the two blocks are distinct. It then rules out a shared pair between their four-vertex unions. Resource containment and disjointness suffice; no extra linearity, exact decomposition or unproved counting injection is assumed.

This is the finite upper half of the combined-family asymptotic result discussed in Glock's Theorem 8. It does not prove that theorem's matching lower half or its asymptotic equivalence.

## Excluded claims

The package does not prove a matching `1/5-o(1)` lower bound, existence of the normalized limit, the general single-family `k` problem, or the cumulative high-girth `1/6` theorem. It does not convert a catalog wording issue into a proof claim. There is no mathematical discovery priority, global first-formalization claim, official verifier signature or award assertion.
