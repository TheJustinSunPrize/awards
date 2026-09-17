# Sources and reuse boundaries

- Andras Gyarfas, *Graphs with k odd cycle lengths*, Discrete Mathematics 103
  (1992), 41-48, [DOI](https://doi.org/10.1016/0012-365X(92)90037-G).
  Mathematical credit for the finite theorem remains with its original author.
- Existing finite Lean proof: [plby/lean-proofs at
  8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos58.lean).
  The source names Codex and GPT-5.6 Sol as formal authors. All 35 modules are
  fetched unchanged; their hashes and imports are recorded by the downloader.
- [Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/58.lean)
  and [cycle definitions](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean).
  Copyright 2026 The Formal Conjectures Authors, Apache-2.0. The definition file
  is byte-identical to Git blob `08b5da1a82f2e4ad251b18d4c94def8fc715f694`.
- [Mathlib compactness](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Compactness.lean),
  formalized by Bhavik Mehta. Graph-coloring compactness is a classical theorem,
  not a mathematical discovery claimed here.
- [Earlier arbitrary-graph submission, PR #130](https://github.com/TheJustinSunPrize/awards/pull/130),
  submitted by MaxwellLaw at 2026-09-16 15:50:58 UTC. Its scope overlaps this
  package's upper bound, equality case, and definition bridge.
- [ReplayBatch.lean](https://github.com/MaxwellLaw/awards/blob/524c5971113fb0405e90534e5709093de7b43f3f/submissions/jsp-000078-MaxwellLaw/ReplayBatch.lean)
  is reused byte-for-byte, SHA-256
  `0ff295a3780e93a6ccd0142d4de9c438a996b162021c79d762d30f22204e3e82`.
  It adapts the Lean checker loading logic by Kim Morrison and Sebastian
  Ullrich; the batch adaptation comes from MaxwellLaw's submission with Codex
  assistance. It calls the unchanged Lean 4.33.0 `Environment.replay` API.
  Its original copyright and license header is retained. The unsafe driver
  is verification tooling and is never imported by the mathematical modules.
- Official [verification guidance](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/docs/verification.md),
  [assessment dimensions](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/docs/grading.md),
  and [problem record](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000078).
  A successful build and contribution credit do not determine an award.
