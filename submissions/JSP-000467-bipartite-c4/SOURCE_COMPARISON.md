# Prior-source comparison

Checked on 2026-09-17. This is a bounded scope comparison, not a global novelty
certificate or an independent verification of third-party proofs.

The original problem page states that every graph on 4k vertices with minimum
degree at least 2k contains k vertex-disjoint four-cycles, and attributes the
proof to Wang (2010). This precisely matches JSP-000467 in the official catalog.

The latest observed `plby/lean-proofs` main commit was
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, equal to the previously saved snapshot.
The following actual sources were read:

- [`Erdos577.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos577.lean):
  55 lines; proves the positive minimum-degree theorem and the product-indexed
  injection formulation. It imports `Erdos577.FinalCount`.
- [`Erdos577/Basic.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos577/Basic.lean):
  223 lines; defines ordinary quadrilaterals as Mathlib C4 copies, defines an
  injective product-indexed packing, and proves the 0/1-cycle base cases.
- [`Erdos577/FinalCount.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos577/FinalCount.lean):
  46 lines; derives the contradiction under the positive minimum-degree bound,
  using `Erdos577.ClaimTwoSeven` and the internal feasible-chain machinery.
- The introductory proof map and dependency discussion in
  [`SOURCE_AUDIT.md`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos577/SOURCE_AUDIT.md)
  were read. It concerns the long Wang proof and its local exchanges.

The fixed tree contains 851 supporting Lean files under `Erdos577/`, approximately
6.9 MB. Their entire dependency closure was not individually read or rebuilt.
GitHub code searches restricted to this directory for `bipartite` and
`completeBipartiteGraph` returned no hits. Searching `sharp` returned an internal
paw-classification file and the source-audit document. Index searches can miss
equivalent results or unindexed content and are not a proof of absence.

Current official awards Issues/PR searches for `577` and `JSP-000467` returned no
matches at the time of screening. This result is time-sensitive.

The specific proposed increment is the exact capacity formula for every K_ab,
including a construction attaining the upper bound, followed by the full
K_(2k-1,2k+1) threshold-obstruction family. These results are not in the main,
basic, or final-count sources read above. This project does not duplicate the
851-module positive-threshold proof and does not claim that no other repository
has formalized the elementary sharpness argument.
