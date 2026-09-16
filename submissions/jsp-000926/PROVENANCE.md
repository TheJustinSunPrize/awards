# Sources, attribution, and bounded duplicate review

This is an incremental formalization contribution for JSP-000926, proposed as Partial Progress. It reuses published mathematics and a public Lean construction; it does not assert global first priority.

## Mathematical sources

- [Erdős Problem 1115](https://www.erdosproblems.com/1115) asks about disk length of asymptotic curves of finite-order entire functions, in particular whether a linear bound is always possible.
- A. A. Gol'dberg and A. E. Eremenko, *On asymptotic curves of entire functions of finite order*, Mat. Sb. 109(151) (1979), 555–581; English translation Math. USSR-Sbornik 37(4) (1980), 509–533. [DOI](https://doi.org/10.1070/SM1980v037n04ABEH001989), [author-hosted paper](https://www.math.purdue.edu/~eremenko/dvi/as-curves.pdf), [Math-Net record](https://www.mathnet.ru/eng/sm2401).

Theorem 1 gives counterexamples with arbitrary divergent loss above the near-Hayman growth threshold. Prescribing the exact finite order is a separate strengthening in Theorem 2. This submission establishes the geometric linear-length counterexample with some finite order, and does not claim the prescribed-order strengthening or the general optimum as a function of maximum modulus. The copyrighted paper is cited, not redistributed or relicensed.

## Existing formalization and license

The prerequisite is [plby/lean-proofs, Erdos1115.lean at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1115.lean). The immutable bytes and length are recorded in [upstream-pin.json](upstream-pin.json); the bootstrap checks both before compilation. The public package imports this prerequisite and fetches it separately, preserving its complete original header.

That header explicitly states Apache 2.0, identifies the file as modified, and credits the mathematical authors above and Codex / GPT-5.6 Sol as formal authors. The repository's [source license notice](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE) and [source metadata](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/data/sources.yaml) were also checked. This file-specific notice is the basis for the attributed adaptation; no license conclusion is inferred for other files in that repository.

The new code retains Apache-2.0 licensing and an explicit modification/provenance notice. `GeometricLength.lean` adapts the gate-hitting part of `labyrinth_isLengthBarrier`, replaces its time estimate by a polygonal-variation lower bound, and reuses the analytic construction by import. Mathlib's bounded-variation infrastructure is separately attributed in [NOTICE](NOTICE). See [LICENSE](LICENSE).

The upstream source mentions `tex/1115.tex`, but that path was absent from the pinned Git tree and its raw URL returned 404 during review. No claim is made to have inspected that missing reconstruction; the checked sources were the Lean file and the original paper.

## Public duplicate review

On 2026-09-17 (Asia/Shanghai), a read-only source review checked the complete two-page snapshot of 150 pull requests in TheJustinSunPrize/awards, timestamped 2026-09-16T23:05:34Z, plus targeted PR, issue, code and web searches for JSP-000926, Erdos1115, geometric arclength and variation. No submitted completion of this particular geometric scope was identified in those checked sources. Search indexing and public visibility are limited, so this is not an exhaustive global absence claim.

The additional relevant code hits were inspected at fixed revisions:

- [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1115Problem.lean) defines the disk-length quantity and counterexample using custom axioms; it does not supply the missing geometric proof.
- [ryantuck/erdos-ai](https://github.com/ryantuck/erdos-ai/blob/f32b2886f8f005d481533036d0af4fe36e8e48f7/conjectures/1115.lean) has a variation-based arc-length path statement, but its main counterexample theorem is unproved. It is not reused as a proof dependency here.

These observations distinguish checked source content from verification claims. No third-party reported build was counted as a successful build of this submission. The source/scope reviews were performed with separate AI agents; they are not human referee opinions or organizer-appointed attestations.
