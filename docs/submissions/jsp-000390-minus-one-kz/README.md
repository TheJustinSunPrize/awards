# JSP-000390: formalization of two known residue families

## September 16, 2026 supplement to the same PR

This contribution now covers the **known k=-1 case and the whole known family
k=2^i for every positive integer i**. The latter is a quantified parameter family,
not a collection of finitely many numerical checks. This is an extension of the
existing PR #260, not a second application or a separate reward request per exponent.

The original k=-1 proof is unchanged. Its [initial submission narrative](INITIAL_MINUS_ONE_README.md),
[statement](STATEMENT.md), and [original verification receipt](VERIFICATION.md) are
retained as historical scope/evidence records. Their "k=-1 only" wording describes
the earlier snapshot, not the enlarged package. See [the supplement](POWER_SUPPLEMENT.md)
for the new exact theorem, mathematical attribution, verification and remaining limits.

## Requested review

Please assess the added formalization for statement correspondence, reproducibility,
attribution, priority and eligibility. The original all-k question is **not solved**.
The mathematics is known: this is not a new mathematical-discovery claim, and no
global first-formalization or financial entitlement is asserted. The new family's
public source has its own publication history; the earlier PR timestamp is not
claimed as its proof-publication timestamp.

Proposed recipient placeholder: `RECIPIENT-JSP-000390-KZ-A`, confirmation pending.
This is the submitting account's AI-assisted self-submission, prepared with OpenAI
ChatGPT assistance, not independent human or organizer verification. The mathematical
credit remains with Graham, D. H. Lehmer and E. Lehmer, and Quanyu Tang's public
expository note is credited for the construction. Existing Lean k=2 work is acknowledged.
The general-base lemma is useful strengthening in this implementation; it is not
claimed as a new mathematical discovery or a separate prize problem.

Only this proposed proof-intake directory is extended. No official catalog status,
candidate or award record, person profile, validator, schema, test or payout status is
changed. Please redirect the intake location if required. The proof-package lakefile
is enlarged only to compile both modules with the same fixed dependency manifest.

## Verification and reproduction

Verified source commit: `7f76545c7ae6a34dcd5b63455012cec87b08223b` in
`ketianzhang1-lang/jsp-000301-lean`, directory `projects/jsp-000390-minus-one`.
[Successful public proof run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35142890158).

Lean 4.34.0 / Mathlib 4.34.0 are fixed. The complete two-module build with warnings as
errors, both bundled kernel replays, twelve actual axiom reports, and the negative
control passed. Strict-allowlist NaNoda checked **24,448 declarations with no errors**,
including the dependency closure of the combined theorem. The pinned source supplies
reproduction scripts; [compact actual reports](power-evidence/power-nanoda.log) are included here.

```sh
sha256sum -c SHA256SUMS
lake exe cache get
lake build --wfail
lake env leanchecker JSP000390
lake env leanchecker JSP000390Power
lake env lean Audit.lean
lake env lean PowerAudit.lean
```

For the exact independent-checker run, use [the pinned reproduction scripts](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7f76545c7ae6a34dcd5b63455012cec87b08223b/projects/jsp-000390-minus-one/scripts)
in the source project.

Network access and official dependency caches were used; all transitive revisions
are locked. No offline full-Mathlib rebuild, independent human signatories, organizer
approval or independent permanent archival is asserted. Full export/build artifacts
have finite retention; exact IDs, byte counts and hashes are in POWER_SUPPLEMENT.md.
