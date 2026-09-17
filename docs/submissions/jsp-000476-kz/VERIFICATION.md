# Observed verification results

All checks below completed successfully on 2026-09-17 UTC.

## Immutable source and run

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Proof commit: `933c76d71c241b7cb078b5acc644188a94798b26`
- Source directory: https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/933c76d71c241b7cb078b5acc644188a94798b26/projects/jsp-000476
- Run: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171337199
- Job: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171337199/job/105043456044
- Lean: `v4.34.0`; Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

## Results

- `lake build --wfail`: passed, 2277 build jobs.
- `lake env leanchecker JSP000476`: passed.
- Twelve target axiom audits: passed; only `propext`, `Classical.choice`,
  and `Quot.sound` occur.
- Nine dependency revision checks: passed.
- Negative control `1 = 0`: rejected, as required.
- Pinned strict NaNoda: **31,556 declarations checked with no errors**.
- Official repository validation, links, generation/check and all 22 tests
  passed locally for this submission package. These checks verify repository
  structure; they do not execute or approve the mathematics.

The CI source of every file listed in PROOF_SHA256SUMS is byte-identical to
the corresponding submission file. Documentation is supplemented here with
observed results, statement comparison and a corrected attribution sentence.

## Artifact receipt and retention

- Archive ID: `10476872050`, name `jsp-000476-evidence`.
- URL: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171337199/artifacts/10476872050
- Byte count: `30102830`.
- SHA-256: `b8730b580a414c6e10cadd940e549888cd997ff10c18a1d064ba84f38d9f64da`.
- GitHub-reported expiry: `2026-12-16T01:38:29Z`.

The ID, size and digest were read from the GitHub artifact API and match the
workflow upload log. A local download from the connector-provided file URL
was blocked with HTTP 403, so no separate local ZIP hash validation is claimed.
The large checker export is subject to the stated GitHub retention deadline;
a permanent independent archive has not yet been established. The proof
source, reproduction scripts, receipt and relevant log excerpt are preserved
in Git. See artifact-receipt.json and verification-excerpt.log.

The exported roots are `exact_criterion`, `multiples_power_free_iff`,
`cubic_lower_bound`, and `example_twelve` in namespace JSP000476, together
with their complete dependencies. The exporter is pinned to
`6cea97789dc088ea47fcea15692db85685aedac5`; NaNoda is pinned to
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. Unpermitted axioms are hard errors.

## Independence and review

NaNoda is an independent checker implementation, but its run was initiated
by the contributor. This is not a claim of independent human review,
organizer verification, recipient confirmation, award approval, or payment
entitlement. Overlap with the existing Erdős 587 formalization is disclosed
in README.md; eligibility for this scoped component remains undecided.
