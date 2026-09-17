# Supplementary implementation and verification for JSP-000476

## English

This supplement attaches a separately written Lean implementation to the existing
[PR #372](https://github.com/TheJustinSunPrize/awards/pull/372).
It covers the same classical multiples construction and is not a second problem
submission, a new complete solution, or an additional award claim. The existing
submission remains the primary package.

For a positive integer m = c²q, with c > 0 and q squarefree, the supplementary
implementation proves that {m,2m,...,km} has no nonempty square subset sum exactly
when k(k+1)/2 < q. For squarefree q, failure of this condition yields a nonempty
subset summing to q². It also proves that k²(k+1) <= N suffices for a k-element
square-sum-free subset of {1,...,N}.

The original problem concerns arbitrary subsets and their extremal asymptotic
size. This implementation does not prove its general upper bound.

## Relationship to the existing submission

| Existing primary theorem | Supplementary theorem | Relationship |
| --- | --- | --- |
| `general_step_criterion` | `square_part_multiples_iff` | Same square-subset-sum classification; the supplementary statement uses the triangular-number quotient. |
| `all_positive_steps_classified` | `exists_classification` | Same uniform classification for every positive multiplier. |
| `exists_power_free_card` | `exists_card_squareSumFree` | The supplementary lower bound excludes squares; the primary result excludes all perfect powers and is stronger. |

Both implementations use Mathlib and were prepared for the same proposed
contributor with OpenAI ChatGPT assistance. Separate implementations and workflow
runs do not constitute independent human review. No claim of priority, mathematical
novelty, or double credit is made.

The classical construction and its squarefree extension are credited to Erdős
and to the discussion in Nguyen–Vu, Example 1.2 and Remark 1.3 of
[Squares in sumsets](https://arxiv.org/html/0811.1311v2).
The supplementary development also acknowledges the inspected
[earlier external Lean lower-bound file](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587/LowerBound.lean).
Original mathematical and formalization credits remain with their respective
authors. The proposed recipient placeholder remains RECIPIENT-JSP-000476-KZ-A,
pending confirmation.

## Pinned supplementary source and evidence

- Tested source commit: `f633b03a38750049758fb67c2f0800bda3c42107`.
- [Exact Lean source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/f633b03a38750049758fb67c2f0800bda3c42107/projects/jsp-000476/JSP000476.lean).
- Proof source SHA-256: `543e9c46142bd9fa8092f1fbdc34c4648cebe0b9e595c1ea045db9b72ae4f67e`.
- [Successful workflow run 35173027153](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173027153), job `105048572235`.
- [Evidence package at commit fd222d6](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/fd222d6d33a00b1904f675fbdb7f1d22e26475e7/projects/jsp-000476).
- [Verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fd222d6d33a00b1904f675fbdb7f1d22e26475e7/projects/jsp-000476/VERIFICATION.md).
- [Machine-readable verification receipt](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fd222d6d33a00b1904f675fbdb7f1d22e26475e7/projects/jsp-000476/evidence/ci-verification.json).
- [Retained exact verification-step log](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fd222d6d33a00b1904f675fbdb7f1d22e26475e7/projects/jsp-000476/evidence/ci-verification.log).
- Log SHA-256: `1dfec36b6fbd2267dd580439b9aad8d9a310061788e74a7b388c8379f3f8dbf4`.

The evidence commit changes only documentation and evidence; its proof source is
identical to the tested source. The workflow artifact is `10477641570`, with digest
`sha256:1f5fe698978e9482d659ae5d673d743917c107c3e9903bf46fa8319e5af8e13c`
and reported expiry 2026-12-16. The committed receipt and textual log remain
available independently of that artifact's retention period; independent archival
preservation has not been established.

## Observed verification and limits

The ordinary GitHub runner used Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation with warnings as failures,
Lean's bundled `leanchecker`, boundary examples, and the transitive axiom audit
for all 20 supplementary project declarations passed. The permitted axioms were
only `propext`, `Classical.choice`, and `Quot.sound`. Every dependency revision
matched the committed manifest. A false arithmetic statement was rejected.
An additional Python check passed all 1,664 tested multiplier/length pairs; this
finite check supplements the general Lean proof.

The supplementary source has not been checked with NaNoda. The primary source's
NaNoda result must not be attributed to this different implementation. Neither
workflow success nor this supplement establishes organizer acceptance, originality,
eligibility, recipient confirmation, or payment entitlement.

Please assess this material together with the existing submission, particularly
its overlap and any incremental formalization value.
