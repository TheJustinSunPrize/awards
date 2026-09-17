# Submission evidence: JSP-000022

## Exact contribution

For every actual state count `N >= 2`, the package constructs a Mathlib
`DFA Bool (Fin N)` whose minimum reset-word length is exactly `(N-1)^2`.
Synchronization means that every initial state reaches the same final state.
The proof covers arbitrary words, and includes the boundary case `N = 2`.

Three trajectory invariants give the lower bound. If `r` is the number of
rotation letters and `e_i` counts effective merges along a trajectory, then
the final state is `i+r+e_i` modulo `N`, `(N-1)e_i+final_i <= r+i`, and
`r+e_i <= |w|`. Synchronization forces a trajectory with `e_i >= N-1`.
The explicit word `b (a^(N-1) b)^(N-2)` attains the resulting lower bound.

Key declarations: `Cerny.reset_length_lower_bound`, `resetWord_resets`,
`resetWord_length`, `exact_reset_threshold`, and `sharp_family`.
The last theorem states that a reset word of length at most `L` exists
if and only if `(N-1)^2 <= L`.

## Mathematical provenance and scope

This formalizes the classical sharp family due to Jan Cerny (1964).
It does not solve the general Cerny conjecture or prove an upper bound for
arbitrary synchronizing automata. No new mathematical result or global first
formalization is claimed. The source comparison records the actual bounded
search, including the Formal Conjectures statement and an inspected
three-state formalization with a different infinite-stream objective.
No candidate-specific proof code from those sources was incorporated.

See `PROOF.md` and `SOURCE_COMPARISON.md` for the proof and fixed-source details.

## Immutable published evidence

- Source: [156631890/cerny-automata-reset-threshold](https://github.com/156631890/cerny-automata-reset-threshold/tree/bef3ac8262806d0d8b1db2e54778052e20f37522).
- Fixed commit: `bef3ac8262806d0d8b1db2e54778052e20f37522`.
- [Release v1.0.0](https://github.com/156631890/cerny-automata-reset-threshold/releases/tag/v1.0.0), release ID `390533578`.
- [Source and verification archive](https://github.com/156631890/cerny-automata-reset-threshold/releases/download/v1.0.0/cerny-automata-v1.0.0.zip), asset ID `569789486`.
- Archive size: `23444` bytes.
- Archive SHA-256: `a84574463f9eeb4286a0cfa0e327229ea126a7796beec20863f5bccad6b18ba5`.
- The uploaded archive was downloaded again and matched the fixed Git source
  and all `13` recorded source/configuration/document hashes.

## Local proof verification

Lean `4.33.1`, release commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
with Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.

- `lake --wfail build Cerny`: exit 0.
- `lake env lean -DwarningAsError=true Audit.lean`: exit 0;
  `10` audited declarations use only standard Lean axioms
  (`propext`, `Classical.choice`, and/or `Quot.sound`).
- `lake env leanchecker --verbose Cerny` with `LEAN_NUM_THREADS=1`:
  exit 0; all `1` local proof modules replayed.
- Actual logs, pinned dependencies, reproduction script, and file hashes are
  included under the package directory. The separate source-level statement
  review is in `statement-review.md`.

Replay uses Lean's own kernel implementation and trusts imported package
artifacts. It is not an independently implemented checker, a fresh replay of
every imported dependency, or a network-isolated verification.

## Attribution and requested review

This is a self-submission by public account `156631890`, requesting review
of the precise formalization above and consideration for any applicable award
category. The proposed contribution recipient is `RECIPIENT-JSP-000022-A`;
recipient identity confirmation remains pending.

Proof development, exposition, local checking and a separate source-level
review used OpenAI Codex and collaborating agents. The review is AI
collaboration, not external specialist review or independent kernel validation.
The package retains mathematical attribution and an Apache-2.0 source license.

In the problem index (`problems/README.md`) at fixed base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`, this entry is marked
`Eligible to claim: No` and `Claim status: Unavailable`. This submission does
not assert existing eligibility or entitlement to payment. It requests an
assessment of the evidenced contribution. No organizer affiliation, committee
conclusion, official verification status, priority determination, award or
payment authorization is claimed.

Only `submissions/JSP-000022-cerny-threshold/` is added. The PR changes no catalog
flag, candidate or award record, recipient profile, or published decision.
No private contact information, identity documents or payment data are included.


This directory is a proposed review-evidence location, not a formal candidate
record. Maintainers may request relocation or external-evidence links only.
The complete source and verification archive is already externally published.

The [first-batch announcement](https://x.com/sunyuchentron/status/2100497325416460762)
was checked on September 17, 2026. This is a later evidence submission, not a
claim to an already announced award. Under the currently published
[v1.0 rules](https://www.hejustinsun.com/zh/prize/rules), completion, first
contribution and eligibility still require assessment. Please clarify whether
this new formalization of a classical component can enter any subsequent
evaluation; no next-batch schedule or acceptance is assumed.

Review and any applicable eligibility decision remain pending. The repository's
CI validates records and links; it does not execute these Lean proofs or decide
awards. No synthetic reviewer or candidate record has been created.
