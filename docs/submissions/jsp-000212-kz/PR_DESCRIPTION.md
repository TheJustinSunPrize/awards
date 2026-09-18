## Expanded contribution

This updates the existing JSP-000212 contribution to the full finite
Bose-Chowla construction: for every prime power q=p^r (r>=1) and every
h>=2, a q-element set in {1,...,q^h-1} has unique h-term multiset sums
modulo q^h-1, including repeated summands. The h=3 specialization implies
the catalog's distinct-three-element-subset lower bound.

This extends the earlier prime-cardinality, integer-equality result.
It remains a known lower-bound component, not a complete solution of the
open extremal problem, an improved bound or new mathematics. It is one
contribution in this PR; no separate reward is requested for the extension.

## Source and attribution

The package is docs/submissions/jsp-000212-kz. Read README.md, PROOF.md and
VERIFICATION.md for the exact statement, source correspondence and scope.
PrimePower.lean and PrimePowerAudit.lean contain the new work.
BoseChowla.lean and Audit.lean are unchanged from the initial version.
The initial submission and verification remain traceable in Git history
and INITIAL_VERIFICATION.md; no backdated priority is claimed.

Mathematical credit: R. C. Bose and S. Chowla (1962/63), Theorem 1.
Independently written Lean formalization with OpenAI ChatGPT assistance,
under the direction of ketianzhang1-lang. This is a self-submission with
a direct interest in the review outcome.
Recipient placeholder: RECIPIENT-JSP-000212-KZ-A, confirmation pending.

## Verification

Proof source commit: 9ef8a063998150500dcdddad81c669c69ed8fa2c.
Verification run:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178083844

Four modules built with warnings as errors; four bundled kernel replays,
ten axiom audits, locked-dependency checks, false-arithmetic rejection and
strict independent NaNoda replay passed (24888 declarations, no errors). The audits include exact endpoint
types and non-prime examples q=4, 8 and 9. See the receipt for declaration
count, artifact metadata, finite retention and verification limits.

All 22 official repository tests and validation, local links, generation
consistency and immutable-history checks passed. Only the submission
package changes; no catalog, candidate, award or verifier status is changed.

## Review request

Please assess statement fidelity, attribution, overlap, incremental
formalization contribution and eligibility. Contributor-run checks are
not organizer acceptance or independent human sign-off. No worldwide
first-formalization priority or award/payment entitlement is asserted.
