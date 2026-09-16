# Attribution and contribution scope — JSP-000378 / Erdős 466

This package is an AI-assisted formalization prepared for review of an incremental contribution. It does not claim that its submitter discovered or first formalized the original mathematical solution. It was prepared with Codex assistance for GitHub account `jinkaizhang236-sketch`. Prior authors are credited as sources; this package does not purport to act on their behalf.

## Mathematical sources

### Graham's construction and the original solved problem

[Erdős Problem 466](https://www.erdosproblems.com/466) records Ronald Graham's solution and the fixed-parameter lower bound for \(\delta=1/10\). It also credits Sárközy's quantitative improvement. The problem catalogue identifies this topic as [JSP-000378](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000378).

The present construction uses the same parabola method with an integer base chosen as a function of \(\delta\). Its all-parameter formal statement is stronger than the inspected fixed-parameter Lean statement, but no claim of new mathematical discovery or global priority is made. No improved quantitative growth bound over Sárközy's work is claimed.

### Odd integral distances

R. L. Graham, B. L. Rothschild, and E. G. Straus, *Are There n+2 Points in E^n with Odd Integral Distances?*, *The American Mathematical Monthly* 81(1), January 1974, pp. 21–25. [DOI: 10.2307/2318906](https://doi.org/10.2307/2318906).

Their classical result excludes four points in the Euclidean plane with all pairwise distances odd integers. This package proves that special case through a Gram-determinant identity and congruence modulo eight, then applies it to half-integer distances. The obstruction is credited to the classical work, not presented as a new discovery.

## Prior Lean source

Repository: [plby/lean-proofs](https://github.com/plby/lean-proofs).

Inspected immutable revision: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.

Source: [`src/latest/ErdosProblems/Erdos466.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos466.lean).

The source itself identifies:

- Ronald Graham as the informal mathematical author;
- Codex and GPT-5.6 Sol as formal authors;
- The Formal Conjectures Authors in the copyright notice;
- Apache 2.0 as the original license, with a notice that the file was modified.

The exact copyright notice to retain with material derived from that source is:

> Copyright (c) 2026 The Formal Conjectures Authors.
> Released under Apache 2.0 license.

That source already gives a complete solution of the original existence question with \(\delta=1/10\). The present package therefore must not be described as the first Lean solution of Erdős 466. Its definitions, nearest-integer interval proof, and compactness strategy are derived from or adapted from the identified implementation. The changed namespace and file organization do not remove that dependence.

The prize repository already contains related evidence in [Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) and a source-register proposal in [PR #40](https://github.com/TheJustinSunPrize/awards/pull/40). Those records and their contributors' evidence work should be linked and credited separately from the present extension.

## File-level contribution map

The following development files are in `source-components/`; their bodies are mechanically assembled into the canonical `Erdos466.lean` without altering the proof text.

| File | Source relationship and additional scope |
| --- | --- |
| `Erdos466Definitions.lean` | Uses the prior Euclidean-plane and nearest-integer conventions. The interval lemma follows the prior proof. Adds or assembles the coordinate and half-integer bridges needed by this package. |
| `Erdos466Arithmetic.lean` | Formalizes the distance interval for an arbitrary parameter and an appropriately chosen base. The underlying parabola construction is credited to Graham. |
| `Erdos466Construction.lean` | Extends the inspected base-two construction to a parameter-dependent base and an injective infinite configuration. Its maximum-cardinality definitions and compactness argument follow or adapt the prior source; the all-parameter limit theorem is the additional scope under review. |
| `Erdos466EndpointArithmetic.lean` | Formalizes the odd-square congruence and planar Gram-determinant identity used in the classical odd-distance obstruction. |
| `Erdos466Endpoint.lean` | Connects that obstruction to the standard Euclidean metric and nearest-integer condition, including the non-strict endpoint. |
| `Erdos466General.lean` | Combines the construction and endpoint bound into the classification for every positive parameter, and derives the original existence question as a corollary. |

All package-specific mathematical and formalization contributions are to be assessed against the final pinned source. A comparison against one identified implementation is not proof that the stronger formulation has never been formalized elsewhere.

## Dependencies and assistance

The package uses Lean and Mathlib; their existing theorems, tactics, and respective licenses remain those of their contributors. The final package pins Lean `v4.34.0` and Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435`. It was initially developed under Lean `v4.33.1`; final validation uses the pinned current release and records actual versions and hashes.

Codex assisted the current formalization, mathematical review, and preparation of the submission materials. The prior source's mention of Codex and GPT-5.6 Sol is retained as historical attribution; it is separate from the current package's assistance disclosure. This document does not assert that OpenAI is the submitter, prize recipient, sponsor, or endorser.

## Licensing and recipient attribution

The Lean source is intended to be distributed under Apache 2.0, consistently with the reused source. Distribution should include the full license, retain the applicable original notices, and identify substantive modifications. This document records provenance; it does not replace the license file.

No recipient identifier or official recipient record is created by this package. Any request for recognition under the submitting account concerns only the supported incremental formalization contribution. Mathematical credit, formalization credit, eligibility, and any award or contribution allocation are distinct determinations.

## Validation status

Lean 4.34.0 compilation, `leanchecker --fresh`, theorem-closure export and Nanoda independent checking all passed on 2026-09-16. Nanoda checked 27,805 declarations with no errors; the only admitted axioms were `propext`, `Classical.choice` and `Quot.sound`. See `verification/verification.public.json` and the logs. Official verification, recipient confirmation, prize eligibility and award decisions remain pending.
