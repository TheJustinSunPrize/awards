## Change

Add a scoped, reproducible Lean formalization for JSP-000057 / Erdős problem
20: the classical sharp rank-two, three-petal threshold `Erdos20.f 2 3 = 7`.
Both sufficiency and the six-edge counterexample are proved, with a bridge
to the original `Set (Set α)` definition. The exact threshold predicate is
also proved equivalent to `7 <= m`, excluding empty-infimum artifacts.

This does **not** resolve the general sunflower conjecture, improve a known
mathematical bound, or assert a first formalization. Please review this as a
scoped community formalization contribution; eligibility is for the committee
to determine. The contribution and prior work are described in
`docs/submissions/jsp-000057-kz/README.md` and `source/PROVENANCE.md`.

Proof commit: `b45035ab53aece620f2029e0e73c7e8146718cd1`.
Verification run: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177146542
Full evidence and artifact identity: `docs/submissions/jsp-000057-kz/VERIFICATION.md`.

## Record or policy impact

No catalog solution/eligibility flag, candidate status, announced award,
recipient confirmation, tier, amount, or payment record is changed.
Recipient placeholder: `RECIPIENT-JSP-000057-KZ-A`; confirmation is pending.
This is a self-submission prepared with OpenAI ChatGPT / Codex assistance.
Prior mathematical work and the original definitions retain their credit.
No global priority claim is made.

## Checks

- [x] English documentation; scoped contribution is not represented as an award.
- [x] Recipient uses a placeholder; no private contact or payment information.
- [x] Pinned Lean source and dependency revisions, eight axiom audits, kernel replay,
      false-statement negative control, and independent strict-allowlist NaNoda check.
- [x] External machine artifact is identified by ID, byte count, and SHA-256;
      finite retention and reproduction instructions are disclosed in the report.
- [x] Existing public statements, decisions, and generated records are preserved.
- [x] Repository validation, links, generation, consistency, history review,
      and all 22 validator tests pass.

## Reviewer decision

Pending. Contributor CI is not organizer verification or award adjudication.
