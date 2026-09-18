# Infinite-family verification receipt — 2026-09-17

This receipt covers the finite-field extension to existing PR #379.

## Pinned source and actual run

- [Proof commit a6b9188dea3d13d3c6c67ea1da6a5fd87045ec7f](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/a6b9188dea3d13d3c6c67ea1da6a5fd87045ec7f/projects/jsp-000443).
- [Successful run 35176333614](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176333614).
- [Successful job 105058746597](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176333614/job/105058746597).
- Exact executed workflow: [PROOF_WORKFLOW_FAMILY.yml](PROOF_WORKFLOW_FAMILY.yml).
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`;
  all nine dependency revisions pinned in lake-manifest.json.

The nine proof/reproduction files listed in
[FAMILY_SOURCE_SHA256SUMS](FAMILY_SOURCE_SHA256SUMS) match the tested source
byte-for-byte. The workflow copy is also hash-listed. JSP000443.lean itself
is unchanged from the initial proof; PolarityFamily.lean adds the algebraic
family and Audit.lean expands from nine to sixteen targets.

| Check | Observed outcome |
| --- | --- |
| Build with warnings as errors | Passed; 3,132 build jobs |
| Lean checker replay | Both JSP000443 and PolarityFamily passed |
| Sixteen axiom closures | Only propext, Classical.choice, Quot.sound |
| All actual dependency Git revisions | Matched the lockfile |
| False arithmetic negative control | Rejected |
| Original finite witness generator | Reproduced the 20 adjacency rows |
| Pinned NaNoda strict allowlist | 21,448 declarations checked with no errors |

NaNoda is pinned to `4c544ed4099c8227f07d5de77ad1e69fb0740a27` and
lean4export to `6cea97789dc088ea47fcea15692db85685aedac5`. Six endpoint
closures are exported, including the universal positive-exponent theorem
`JSP000443.c4StarRamsey_power_two` and both Mathlib graph-copy bridges.
No sorryAx, custom proof axiom or compiler-trust axiom is allowed.
The sixteen-target audit additionally checks the arbitrary-finite-field
lower bound, exact even-field result, and the 64 and 256 specializations.

Compact evidence: [cloud excerpt](family-evidence/ci-excerpt.log),
[run status](family-evidence/run-status.json),
[job status](family-evidence/job-status.json),
[local audit](family-evidence/local-audit.log), and
[local kernel replay](family-evidence/local-kernel.log).
The cloud excerpt is selected from the actual job log; it is not the full log.

## Artifact and reproducibility limits

[Artifact 10479055490](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176333614/artifacts/10479055490)
contains source, lockfile, logs, compressed proof export and checker configuration.
The [service metadata](family-evidence/artifact-metadata.json) reports:

- ZIP size: 17,716,297 bytes.
- ZIP SHA-256: `56cb74e591bd0efe9d4f4340a6d511fa1ba38f60996cbe36267e7d05591b7fcd`.
- Created: 2026-09-17T02:59:58Z.
- Advertised expiry: 2026-12-16T02:57:06Z.

The upload log agrees with the API digest and byte count. These are
service-reported artifact values; a separate local ZIP download/hash check
is not claimed. Git preserves the sources and compact receipts, but the
Actions archive has finite retention and is not an independent permanent
archive. Reviewers can retain it or rerun the pinned scripts.

The run used Ubuntu 24.04, network access and cached Mathlib artifacts.
There is no claim of an air-gapped rebuild of every imported library.
NaNoda is an independently implemented checker run by the contributor;
this is not independent human or organizer certification.

## Submission repository checks

Record validation, Markdown links, deterministic data generation, consistency,
history preservation and all 22 repository tests passed against official base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. The existing initial verification
receipts and original PR text are retained separately. Changes remain confined
to this submission directory. Earlier same-problem PR #134 and its distinct
Boza theorem statements are acknowledged in PROVENANCE.md.

The original all-parameter problem and unbounded-deficit question remain
outside scope. Contribution significance, attribution, priority and award
eligibility require organizer review.
