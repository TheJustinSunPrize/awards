# JSP-000295: known square-root lower bound, submitted for review

This contribution formalizes the known bound `f(n) >= (2+o(1))*sqrt(n)` for
Erdos 357 / JSP-000295. It proves the stronger explicit inequality
`f(n) >= 2*Nat.sqrt(n)-1` for every natural n.

**Partial scope relative to the original problem:** this does not prove
f(n)=o(n) or determine the exact growth rate. The catalog's overall Progress
status and eligibility flags are not changed.

## Proof and scope fidelity

The witness consists of the `2*t+1` consecutive integers from `t^2+1` to
`(t+1)^2`, for every natural t. The Lean proof covers every pair of consecutive
index intervals, including the empty-set boundary, and establishes boundedness
of the admissible-length set before using its supremum.

`Compatibility.lean` reuses the exact mathematical definitions and theorem type
from the pinned Formal Conjectures statement, omitting metadata attributes.
The proof applies by definitional equality. Read [PROOF.md](PROOF.md) for the
construction, attribution, source links and reproduction commands, and
[VERIFICATION.md](VERIFICATION.md) for the actual completed checks and limits.

Pinned proof source:
[commit 59c5b55, projects/jsp-000295](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/59c5b5540c469b13e7b4848c7c3fbd17e688f519/projects/jsp-000295).

## Attribution and review request

The known lower bound remains attributed to Desmond Weisenberg, following the
pinned Formal Conjectures statement. The two definitions and target type are
adapted from the Formal Conjectures Authors (2025), under Apache 2.0. This proof
implementation was independently written with OpenAI ChatGPT assistance.
Neither new mathematics nor worldwide first-formalization priority is claimed.

Proposed recipient: `RECIPIENT-JSP-000295-KZ-A`; confirmation pending.
This is a self-submission for formalization-contribution review, not an
independent review or award announcement. Please assess statement fidelity,
original contribution, attribution, overlap, intake placement and eligibility.
No prize level, award allocation or payment entitlement is asserted.

The package only adds files under `docs/submissions/jsp-000295-kz/`; it changes
no existing catalog, candidate, award, profile, schema, validator or test file.

## Duplicate screening

At preparation, the official repository search for `JSP-000295` returned no
issue or PR; a second search for `357` and `sums` also returned none. The
inspected public plby/lean-proofs tree had no Erdos357 module. The pinned Formal
Conjectures file stated the known lower bound with a proof placeholder. These
observations motivate this submission but do not establish global priority.
