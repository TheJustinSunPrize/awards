# JSP-000692 / Erdős 836, question 2

## Scope and verification status

The proof sources have now compiled locally with Lean 4.19.0 and Mathlib v4.19.0,
in modular and standalone form. All nine audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. See the source-bound
[receipt](verification/status.json). These are submitter-produced checks, not
independent review or organizer verification. The original candidate was
uncompiled when supplied; its Lean source files have not been changed.

The first question, concerning the number of active vertices, is a separate
assertion. Alon's counterexample addresses it; that first question's Lean proof
is not included or claimed here. This development addresses the unresolved
mathematical step identified in the preceding conversation, namely question 2.

## The stronger theorem

Let H be a finite r-uniform intersecting hypergraph, where r >= 2. Suppose H
has no proper two-colouring. Then there are **distinct** edges E,F such that

    2 |E ∩ F| >= r - 1.

Consequently there is a distinct pair with

    |E ∩ F| >= r / 3,

which answers the linear-bound question with the universal constant c = 1/3.

All vertex sets below are finite. One may restrict the ambient set to the union
of the edges. Adding isolated vertices has no effect on this argument.

## 1. An extremal set containing exactly one edge

Fix an edge E. Among the vertex sets R which contain E and contain no other
edge, choose one of maximum cardinality. Such sets exist: R=E is admissible,
because two different edges of the same cardinality cannot contain one another.
Finiteness guarantees the maximum.

Write Q=V\R. For every y in Q, maximality of R supplies an edge F_y different
from E with

    F_y ⊆ R ∪ {y}.

Indeed, otherwise R∪{y} would still contain exactly E. In particular, F_y
has no vertices in Q other than possibly y. It must actually contain y,
since otherwise it would be a second edge already contained in R.

## 2. Witnesses obtained by removing a point

For every x in E, the set R\{x} contains no edge: its only possible edge
inside R would have been E, and x has been removed.

Two-colour V with R\{x} red and Q∪{x} blue. Since H has no proper
two-colouring and the red class contains no edge, there is an edge G_x with

    G_x ⊆ Q ∪ {x}.

Because H is intersecting, G_x intersects E. But E⊆R and its only possible
intersection with Q∪{x} is x. Therefore

    G_x ∩ R = {x}.

In particular, x∈G_x, |G_x\{x}|=r−1, and the edges G_x are pairwise
distinct as x ranges over E.

Notice that this argument uses **non-two-colourability**, not merely the
existence of a proper three-colouring.

## 3. A square zero-one matrix

Let s be any nonnegative integer which bounds every intersection of distinct
edges. Choose x0∈E and set

    A = E\{x0},       B = G_x0\{x0}.

Both A and B have exactly n=r−1 elements, and B⊆Q.

Define an A-by-B zero-one matrix by

    M[x,y] = 1  if y∈G_x,
             0  otherwise.

### Every row has at most s ones

For x∈A, a one in column y means y belongs both to G_x and to G_x0.
These two edges are different, since their intersections with R are {x}
and {x0}, respectively. Thus the number of ones in row x is at most

    |G_x ∩ G_x0| ≤ s.

### Every column has at most s zeros

Fix y∈B, and consider the edge F_y from step 1. Suppose M[x,y]=0,
so y∉G_x. Since F_y⊆R∪{y} and G_x∩R={x}, their intersection can only
contain x or y. It is nonempty by the intersecting property. The point y
is excluded, so x∈F_y.

Hence the zero entries in column y have row indices contained in E∩F_y.
The edge F_y is different from E, so there are at most s such indices.

## 4. Counting all matrix entries

There are n² entries. Counting ones by rows gives at most ns ones.
Counting zeros by columns gives at most ns zeros. Therefore

    n² ≤ 2ns.

Because n=r−1>0, it follows that

    r−1 ≤ 2s.

This proves the stronger maximum-intersection bound. Equivalently, if every
distinct pair were to satisfy 2|E∩F|+1<r, putting s=⌊(r−2)/2⌋ would contradict
the displayed inequality. This latter formulation is used in Lean to avoid
introducing an explicit maximum over edge pairs.

## 5. A constant valid for every r>=2

Choose the pair given by 2t+1>=r, where t=|E∩F|. Intersectingness gives t>=1.
Thus

    r ≤ 2t+1 ≤ 3t.

So t>=r/3, with no exceptional small ranks and with E≠F explicit.
The bound (r−1)/2 must not be misstated as r/2: those are different statements.

## Translation to Lean

The modules are `JSP692/Hypergraph.lean` and `JSP692/LinearIntersection.lean`.
The latter has these theorem dependencies:

1. `square_matrix_bound`: the finite matrix-counting lemma.
2. `exists_maximal_only_edge`: finite maximization of a unique-edge vertex set.
3. `edge_disjoint_of_independent`: non-two-colourability gives the opposite edge.
4. `edge_meets_only_set_at_point`: constructs G_x.
5. `rank_le_twice_intersection_bound_add_one`: constructs both witness families,
   the matrix, and proves r<=2s+1.
6. `large_intersection_nat`: obtains a distinct witness pair.
7. `large_intersection_one_third`: converts to the real-number bound.
8. `jsp000692_question_two`: states the full universal quantifiers with c=1/3.

There is no unproved "linear-bound lemma" supplied as an extra hypothesis.
Classical choice selects witnesses only after their existence has been proved.

## Attribution and priority

The supplied candidate presents the extremal unique-edge colour-class argument
and witness-matrix double count described above. A previously posted result
has also been located: the Erdős Problems forum
records a claim by Liam Price / GPT-5.5 Pro on 27 April 2026, with a preliminary
check by Nat Sothanaphan on 28 April. The candidate's Overleaf body and the linked
check could not be retrieved. No comparison of proofs, priority claim, novelty
claim, or prize entitlement is made here.

Primary claim location:
https://www.erdosproblems.com/forum/thread/836#post-5941

Original read-only manuscript link recovered from the forum HTML:
https://www.overleaf.com/read/bhnhxhswnjht#52529b

Read-only discussion-check link:
https://chatgpt.com/share/69f0cf09-dff4-839e-8e7e-3951d02cd332

Forum HTML snapshot used to recover the links:
https://github.com/erichou1/erdos-open-problems/blob/4b4ec96f1c81492af02f814c65825a5106e0af60/forum_threads/836.html
