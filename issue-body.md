## Summary

This issue registers the **verification-only** recipient claim for
**JSP-000127** — Erdős problem 119 (https://www.erdosproblems.com/119,
historical bounty $100). The full verified-pending record is in the candidate
PR (branch `candidate/jsp-000127`).

**Problem.** If all zeros of a polynomial lie on the unit circle, how does its
maximum modulus on the prescribed region grow with its degree?

**Lean proof (pinned).** plby/lean-proofs @
`1268917deaaaa0d674f651287027baa26cea9920`, file
`src/latest/ErdosProblems/Erdos119.lean` (1788 lines, single-file closure over
mathlib). Verified against the current release — Lean v4.34.0 / mathlib
v4.34.0 — compile exit 0 (entry + audit modules), axiom audit exactly
`[propext, Classical.choice, Quot.sound]` on all four exported declarations,
2 documented porting patches (PORTING-DIFF-127.md), all artifacts
SHA-256-pinned (hashes-final.tsv).

**Attribution (credit only).** Informal solution: ChatGPT 5.6 Pro, Samuel
Korsky. Statement: Formal Conjectures authors. Formalization: Codex, Boris
Alexeev. Public port: plby. No authorship claim by the recipient.

## Recipient

| Field | Value |
| --- | --- |
| GitHub | shunfeng8421 |
| Name | 陈世强 (Chen Shiqiang) |
| Contribution | Independent verification of the pinned Lean formalization on the current-release toolchain and preparation of this submission |
| Credit | Verification only — no mathematical or formalization authorship claimed |

## Notes

- Catalog status for JSP-000127: Solved, Lean proof: Yes, Eligible: Yes,
  Claim status: **Unclaimed** (checked 2026-09-19).
- No competing submission exists: the earlier [Recipient] issue #191
  (Neo7672) was withdrawn by its author on 2026-09-17.
- Awaiting recipient confirmation; this is a candidate record
  (`status: pending-recipient-confirmation`).
