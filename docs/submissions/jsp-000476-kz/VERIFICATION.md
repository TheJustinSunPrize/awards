# Observed verification — revision 2

All checks passed on 2026-09-17 UTC. The revised proof covers every positive
integer step d through d=b^2*a with a squarefree. The earlier prime-step
theorems and uniform lower bound are retained.

## Source and results

Proof commit: `4ab28a44e7c89d814699c70f79a0e138f72162e7`.
Source: https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/4ab28a44e7c89d814699c70f79a0e138f72162e7/projects/jsp-000476

Run: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172595984
Job: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172595984/job/105047255472

- Lean 4.34.0, Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
- Build with warnings as errors: passed (2277 jobs).
- Lean kernel replay with leanchecker: passed.
- Twenty target axiom audits: passed; only propext, Classical.choice and Quot.sound.
- Nine dependency revision checks: passed.
- False arithmetic negative control: rejected as required.
- Strict NaNoda: **32,032 declarations checked without errors**.
- Official repository validate, links, build/check and all 22 tests passed locally.

The eight exported roots and their complete dependency closures include
the general-step criterion, the all-positive-step classification, the
squarefree perfect-power criterion, and the counterexample {8}. The exact
roots, checker settings and tool commit pins are in scripts/verify_nanoda.sh.
The submission proof, audit and verification scripts match the CI source
byte for byte. Configuration and dependency pins remain unchanged.
PROOF_SHA256SUMS records the exact file bytes.

## Archive receipt and limits

Artifact ID: `10477376441`.
URL: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172595984/artifacts/10477376441
Size: `30500568` bytes.
SHA-256: `6c3184bce60ec757b0cca74a939a1329cab6573527bb4c9e2792e075c0d76b29`.
GitHub-reported expiry: `2026-12-16T01:58:24Z`.

The API receipt and upload-log digest agree. No independent local ZIP
hash validation is asserted. Large exports remain subject to GitHub retention;
permanent independent archiving is outstanding. The source, scripts, receipt
and selected log lines are retained in Git. See artifact-receipt.json and
verification-excerpt.log.

Revision 1 evidence is retained in VERIFICATION-v1.md, artifact-receipt-v1.json,
verification-excerpt-v1.log and Git history.

NaNoda is a separate checker implementation, run by the contributor.
Independent human review, organizer approval, recipient confirmation and
award eligibility remain pending. The original arbitrary-set asymptotic
upper bound is not claimed. Prior mathematical and formalization credit is
preserved in README.md.
