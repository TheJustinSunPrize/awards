# Independent source and statement review

Review date: 2026-09-17. Reviewer: a separate Codex agent that did not author the
five proof modules. This is a source-level mathematical and statement audit,
not an independently implemented second kernel. The reviewer did not modify
the proof files or rerun their already-recorded build.

## Scope checked

All five local Lean modules, `README.md`, `PROOF.md`, `Audit.lean`, and the
recorded `verification/result.json` were read. Mathlib's `Copy` and `cycleGraph`
definitions were checked in the pinned local dependency. The source hashes
below bind this review to the actual files inspected.

Publication note: the hashes in the following table have been updated to the
LF-normalized publication bytes. A byte comparison established that each of the
five proof modules differs from its reviewed version only by CRLF-to-LF line
ending normalization. `verification/normalization.json` preserves the original
and published hashes. No Lean term, definition, statement, or proof was changed,
and the previously recorded checks were not presented as a new execution.

| File | SHA-256 |
| --- | --- |
| `BipartiteC4.lean` | `6843326a45d4061f9363628a689bc07f50c691c6a18c3fe38cf8e7b21c0bbdc2` |
| `BipartiteC4/Basic.lean` | `575af26b677b5df28a89b74ed8319b8b076766e841cf3a2637e64c13b38e77f8` |
| `BipartiteC4/Counts.lean` | `6a597aa73cc87549cecefc0ff01ba60fdad1ab7d4e1cc2b5d06419dce8c209b1` |
| `BipartiteC4/Construction.lean` | `e4e7d4227d4be894c1fd62e3d2d6a188f454d5e9eae1e5241d495ad23203ae12` |
| `BipartiteC4/Sharpness.lean` | `eeecc7d1c90caa642d7bf2918cf4fa8a98fc9eee9bd1844467db7f29e7a8d72e` |

## Packing quantifiers and graph meaning

`HasPacking G k` is `Nonempty (Packing G k)`. The structure imposes only a
global injection from `Fin k × Fin 4` to vertices and the four cyclic adjacency
conditions for every cycle index. It does not require a canonical orientation,
a designated left starting vertex, or the particular lower-bound construction.
The sum type `Fin a ⊕ Fin b` keeps the two bipartition classes disjoint, and
`graph a b` is Mathlib's actual complete bipartite graph.

The global injection enforces both four distinct vertices within each copy and
disjoint vertices across different copies. `Packing.cycle` turns every member
into a Mathlib `(cycleGraph 4).Copy G`, and `Packing.disjoint_cycles` proves the
range disjointness. Mathlib `Copy` is an injective graph homomorphism, so ordinary
cycles are correctly represented without demanding an induced subgraph.

`cycle_adj` correctly converts the modular adjacency of `cycleGraph 4` into the
two possible cyclic successor orientations. `Packing.cycle` handles the reverse
orientation through symmetry, including the closing edge from position 3 to 0.
The representation also describes an arbitrary labelled family of pairwise
vertex-disjoint four-cycle copies: their four vertices can be indexed by `Fin 4`
and their members by `Fin k`. A separate converse conversion theorem from an
external finite-set packing definition is not claimed by this project.

## Universal upper bound

`cycle_left_count` proves that any cyclically adjacent four positions in this
graph have exactly two positions in the left class. It does not need
injectivity for the alternating-class count. The global injection is then used
where needed: `Packing.left_bound` identifies the cardinality of the image of
all left positions with `2*k` and compares it to the actual left class of size
`a`. `Packing.swap` transports arbitrary packings across the class swap, giving
the corresponding bound `2*k <= b`.

These statements quantify over every `Packing (graph a b) k`. The upper bound
is not restricted to the explicit packing later constructed.

## Attainment and exact capacity

`canonicalVertex` assigns the cycle indexed by `i` the ordered vertices
`(A_(2i), B_(2i), A_(2i+1), B_(2i+1))`. The supplied bounds `2*k <= a,b` prove
that each coordinate exists. The proof checks all positions for global
injectivity and all four edges for adjacency. Distinct cycle indices cannot
reuse a vertex.

`hasPacking_iff` combines the universal obstruction with this constructor.
`exact_capacity` is a logically equivalent floor-division reformulation;
`maximum_attained` both supplies a packing at the stated capacity and bounds
every other packing. The declarations include `a=0`, `b=0`, and `k=0` without
introducing positive-size assumptions.

## Degree and order boundary

`degree_left` and `degree_right` compute actual neighbor-finset cardinalities.
`min_degree` requires both bipartition classes to be nonempty before selecting
witness vertices to attain the minimum. `sharpness` supplies those positivity
hypotheses from `k>0`.

For `K_(2k-1,2k+1)`, the four conclusions are the actual order `4*k`, actual
Mathlib minimum degree `2*k-1`, existence of a `k-1` packing, and nonexistence
of a `k` packing. The positive-k hypothesis is present throughout the truncated
natural-subtraction calculations. At `k=1` this is `K_(1,3)`, with degree 1 and
capacity 0, so the small boundary has the intended meaning. The claim is not
mistakenly extended to `k=0`.

`necessary_degree_threshold` assumes a threshold implication for every finite
simple graph of order `4*k` and instantiates it with the obstruction graph.
It concludes only the necessary inequality `2*k <= d`. It does not assert the
positive threshold theorem. `arbitrarily_large_sharpness` selects `k=N+1`, so
it supplies witnesses above each requested size bound and is not a finite
enumeration.

## Finding and limits

No statement mismatch, hidden construction-only upper-bound assumption, missing
global disjointness requirement, or degree/order boundary error was found in
the reviewed source. Its exact complete-bipartite capacity theorem and the
classical necessary-threshold family match the README and mathematical proof.

The recorded build, 14-declaration axiom audit, and five-module replay each have
exit code 0. These are existing machine-verification records; this review adds
a separate reading of the meanings of the declarations. Neither this report
nor the same-kernel replay independently validates the implementation of Lean,
all imported Mathlib caches, formalization priority, or award eligibility.
