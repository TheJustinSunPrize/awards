# JSP-000301 — proof submission for operator review

## English

This intake package contains the Lean source for the exact yes/no question in
[JSP-000301](../../problems/catalog-0301-0400.md#JSP-000301).
The source proves that 12167 and 12168 are consecutive positive powerful
integers and neither is a square, then disproves the universal assertion.

The mathematical counterexample is already in the catalog. This submission
claims a formalization contribution only, not discovery of the counterexample.
It does not address the different counting problem in Erdős problem #365.
The formalization was prepared with Codex AI assistance.

### Source and reproduction

- [Proof source](Proof.lean), [toolchain](lean-toolchain), [verification script](verify.sh).
- [Local verification evidence and limitations](VERIFICATION.md).
- [Immutable upstream source](https://github.com/56647563/jsp-000301-lean-proof/tree/6cb739bbb676a44223111e1f6f627241191862a0).
- [Local reproduction log](https://github.com/56647563/jsp-000301-lean-proof/blob/6cb739bbb676a44223111e1f6f627241191862a0/reproduction.log).
- [Source hashes](https://github.com/56647563/jsp-000301-lean-proof/blob/6cb739bbb676a44223111e1f6f627241191862a0/SHA256SUMS).
- [Versioned source archive](https://github.com/56647563/jsp-000301-lean-proof/releases/tag/v0.1.0):
  `jsp-000301-source-v0.1.0.tar.gz`, 5448 bytes,
  SHA-256 `6405678b61d6a6887aefe73c838d706b14f4b8dd864bc834c0e60d7663cdaf86`.
  This GitHub release is not a permanent third-party archive or DOI deposit.

With official Lean 4.34.0 on PATH, run `sh verify.sh` from this directory.
The bundled Std is the only library dependency. Both main theorems passed local
compilation and a separate bundled `leanchecker` replay; both axiom reports are
`[propext, Quot.sound]`. These are local checks, not an independent verifier's
attestation or proof of prize eligibility. The two tools use the same kernel.

### Requested review

Please determine whether a new 2026 formalization of this known, elementary
result is eligible and identify the correct submission/verification route.
This `submissions/` path is a proposed intake location, not an existing official
workflow designation; the package can be moved to the operator's preferred path.

No public candidate or award record is created by this PR. The catalog states
that the original proposal and first-counterexample dates are unverified, while
the candidate schema requires an integer `problem.posed.year`. No year has been
invented to satisfy that field. The signed formal-statement and verification
records also require authorized curators/verifiers; this submission does not
create profiles or signatures on their behalf.

Please advise how these missing historical dates should be recorded and assign
the necessary statement and verification review if the contribution is eligible.
The mathematical statement and all definitions are explicit in the submitted
Lean file, even though no curator-issued statement record is asserted.

### Attribution and status

Proposed formalization contributor: `RECIPIENT-jsp-000301-A`, confirmation pending.
The account publishing the source is the submission account, not an official
recipient designation. Original solver attribution remains with the existing
result; its first discoverer is not established here.

This is a self-submission; local verification was performed as part of the same
AI-assisted workflow and must not be counted as independent review.
No awarded tier, eligibility flag, claimed state, payment, or official priority
timestamp is asserted. Existing problem-bank and award records are unchanged.
