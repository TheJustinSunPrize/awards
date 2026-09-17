## Revision 2 — classification for every positive step

For every positive integer d, writing d=b²a with a squarefree, the set
{d,2d,...,md} is square-sum-free if and only if m(m+1)<2a.
The proof gives this classification uniformly for all m. For squarefree
steps, the same condition excludes every perfect-power subset sum.
For general steps only squares are excluded: {8} is a formally verified
counterexample to the stronger assertion.

The earlier prime-step results and explicit uniform lower bound are retained.
This classifies the construction family, not arbitrary finite sets or the
original problem's full asymptotic upper bound.

Package: docs/submissions/jsp-000476-kz
Proof CI: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172595984
Pinned proof: 4ab28a44e7c89d814699c70f79a0e138f72162e7.

Lean build, kernel replay, twenty axiom audits and strict NaNoda passed:
32,032 declarations checked without errors. All 22 official repository tests
passed locally. See README.md, STATEMENT.md, CHANGES.md and VERIFICATION.md.

Erdős's construction and Nguyen–Vu Example 1.2 / Remark 1.3 provide the
mathematical context. Prior external Lean work remains acknowledged.
No mathematical novelty or first-formalization priority is claimed.
OpenAI ChatGPT assistance is disclosed. Proposed recipient:
RECIPIENT-JSP-000476-KZ-A, confirmation pending.

Please assess fidelity, attribution, overlap, incremental contribution and
eligibility. Contributor checks are not organizer approval or payment
entitlement. The artifact receipt states its retention deadline; permanent
independent archiving remains outstanding.

## Previous revision

Original proof and evidence are preserved in Git history and files ending
in -v1. Original CI:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171337199
