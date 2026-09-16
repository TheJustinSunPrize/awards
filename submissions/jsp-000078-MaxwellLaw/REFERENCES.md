# References and reuse boundary

## Mathematics

1. **András Gyárfás**, *Graphs with k odd cycle lengths*, Discrete Mathematics **103** (1992), 41–48. [DOI and publisher record](https://doi.org/10.1016/0012-365X(92)90037-G); [author-hosted paper](https://www.renyi.hu/~gyarfas/Cikkek/57_Gyarfas_GraphsWithKOddCycleLengths.pdf). This is the mathematical source of the finite structural theorem, chromatic bound, and equality case. The conjecture is attributed to Bollobás and Erdős on the [Erdős 58 problem page](https://www.erdosproblems.com/latex/58).
2. **N. G. de Bruijn and Paul Erdős**, *A colour problem for infinite graphs and a problem in the theory of relations*, Proceedings of the Section of Sciences of the Koninklijke Nederlandse Akademie van Wetenschappen, Series A **54** (1951), 371–373. [Institutional record and original paper](https://research.tue.nl/en/publications/a-colour-problem-for-infinite-graphs-and-a-problem-in-the-theory-/). The general-graph extension uses this classical compactness principle; no new mathematical compactness theorem is claimed.

## Existing formalization

3. **The Lean-Proofs Authors**, finite Erdős 58 formalization in `plby/lean-proofs`, pinned to commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. [Main theorem and published credits](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos58.lean); [dependency directory](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos58); [original addition by Boris Alexeev](https://github.com/plby/lean-proofs/commit/27b78c6ced9e02f789380a472e072d5081580c8c). The main header lists **András Gyárfás** as informal author and **Codex / GPT-5.6 Sol** as formal authors. The complete 35-module import closure is vendored **byte-for-byte unchanged**, with per-file SHA-256 and byte counts in [vendor-manifest.json](vendor-manifest.json). Existing copyright and license headers are retained. Its exported theorem has the explicit hypothesis `[Finite V]`.
4. **Bhavik Mehta and the Mathlib contributors**, [Combinatorics/Compactness.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Compactness.lean). We invoke `Finset.rado_selection_subtype`; its proof is imported from Mathlib, not reimplemented or attributed to MaxwellLaw. The source itself references Rado's 1949 selection principle and de Bruijn–Erdős (1951).
5. **The Formal Conjectures Authors**, [Erdős 58 statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/58.lean) and [cycle-length definitions](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean), commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. The latter file is unchanged and relocated to `Jsp000078/CycleLengths.lean`. Its Apache 2.0 notice remains intact. The final theorem uses the same statement and definitions; `oddCycleLengths_eq` bridges them to the finite source.

## This submission

- Human submitter / GitHub identity: [MaxwellLaw](https://github.com/MaxwellLaw).
- AI assistance: OpenAI Codex assisted with source review, the new Lean proof, debugging, verification commands, and documentation. This is not an independent human verification claim.
- New proof code: `Jsp000078/Compactness.lean` and `Jsp000078/General.lean`.
- New supporting work: package configuration, source hashes, audit, reproduction instructions, and submission documentation.
- Reused work: all `ErdosProblems/` source files, `Jsp000078/CycleLengths.lean`, Lean and Mathlib. These remain credited to their respective authors.
- No claim is made to the mathematical discovery, the pre-existing finite formalization, exclusive first-publication priority, award eligibility, or an award decision.

## Verification utility

6. **Kim Morrison and Sebastian Ullrich**, [Lean 4.33.0 LeanChecker.lean](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/LeanChecker.lean). [Replay.lean](Replay.lean) retains the original copyright notice and copies `replayFromImports` unchanged; only the command-line driver is adapted to replay exact module names sequentially. It is a separate verification utility and is not imported by the mathematical proof. This reuses the same Lean kernel and is not an independent implementation of a verifier.

7. [ReplayBatch.lean](ReplayBatch.lean) adapts the module-data loading logic from the same LeanChecker source and calls the unchanged [Lean.Environment.replay](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Replay.lean) API, by **Kim Morrison**. It collects every declaration in the specified modules and replays them together into a Mathlib-only environment. It rejects overlapping names, unsafe/partial declarations, and custom axioms. This avoids repeated imports while keeping every custom declaration subject to kernel checking. The original copyright notice is retained.
