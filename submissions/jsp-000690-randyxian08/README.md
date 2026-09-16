# JSP-000690: Lean formalization submitted for review

This package formalizes the affirmative weak-chromatic interpretation of
[JSP-000690](../../problems/catalog-0601-0700.md#JSP-000690), also
[Erdős problem 834](https://www.erdosproblems.com/834).
The explicit construction and deletion certificates are due to Ruiliang Li,
[arXiv:2512.24850v1](https://arxiv.org/abs/2512.24850v1), Theorem 4.1 and
Appendices A–B. Mathematical discovery credit remains with the original author.

The main declaration `JSP690.JSP_000690_full` proves the existence of a simple
3-uniform hypergraph on 9 vertices with 22 edges, chromatic number exactly 3,
every proper subhypergraph 2-colorable, and minimum degree exactly 7.
See [statement correspondence](STATEMENT.md) and [verification review](REVIEW.md).

## Reproduce

Install `leanprover/lean4:v4.19.0` with Elan, or put the official standalone
Lean 4.19.0 binaries on PATH. Python 3.10 or newer is required; no external
Python packages or Mathlib are needed for the proof package.

```sh
cd submissions/jsp-000690-randyxian08
bash verify.sh
```

The script runs 11 auxiliary audit tests, checks the finite data, performs a
clean Lean build, checks the source directly, and audits four declarations.
The actual local receipt is [verification/status.json](verification/status.json).
Logs record submitter-produced checks, not organizer or independent certification.
`SHA256SUMS` describes the submitted snapshot; rerunning verification updates
some timestamped evidence files.

## Attribution and related submissions

The submitting account is `randyxian08`. Preparation, compatibility repairs,
proof review, and verification used OpenAI Codex assistance. The proposed
formalization recipient identifier is `RECIPIENT-JSP-000690-A`, pending the
organizer's confirmation procedure. This is a formalization contribution only.

Existing related submissions were found before this submission:
[issue #15](https://github.com/TheJustinSunPrize/awards/issues/15),
[PR #21](https://github.com/TheJustinSunPrize/awards/pull/21), and
[PR #35](https://github.com/TheJustinSunPrize/awards/pull/35).
No first-formalization claim is made. This separate package is supplied for
comparison and review; no duplicate problem record is proposed.
The submitter has an interest in evaluation of this formalization contribution.
No affiliation with the other submitters or the original author is asserted.

## Requested review

Please assess the formal statement, reproduce the proof, compare attribution
and priority with the existing submissions, and determine prize eligibility.
The mathematical paper was first submitted on 2025-12-31; this formalization
and its local verification are submitted in 2026. Eligibility under the rules'
2026 cutoff is left for the organizer to decide.

This directory is a proposed intake location. Please redirect it if another
path or repository is required. No official candidate/award status, catalog
eligibility flag, recipient profile, or reviewer signature is changed.
The repository's existing CI validates repository records, not this Lean proof.
