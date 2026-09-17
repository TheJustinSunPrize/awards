# Verification receipt for the finite-color supplement

The following are observed contributor-run checks. They do not establish
independent human review, organizer acceptance, eligibility or an award.

## Fixed source and execution

- Proof commit: `0175b2a7a50f7687ece92f61bbe0e3a2f377913a`.
- Proof Git tree: `db4ac2ff6999713bbafe16fdd87c7c7a8949f789`.
- [Successful run 35177218300](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300).
- [Successful job 105061458531](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300/job/105061458531).
- Completed 2026-09-17 UTC; Lean 4.34.0; Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

The complete locally prepared proof Git tree matches the uploaded tree above.
The two Lean files copied in this supplement match their pinned proof-project
counterparts byte-for-byte; [PROOF_SHA256SUMS](PROOF_SHA256SUMS) records their
hashes. The original 27 files in PR #408 were checked against its prior head
`167ed0362b8041f5b3b52fde8bcac8be6a1755bf`; this supplement does not modify them.

| Check | Observed result |
| --- | --- |
| Compile with warnings treated as errors | Success; 3,133 build jobs |
| Bundled Lean kernel replay of `Multicolor` | Success |
| All nine named axiom closures | Only `propext`, `Classical.choice`, `Quot.sound` |
| Actual dependency Git revisions against the lockfile | All matched |
| False-arithmetic negative-control gate | Passed |
| Independent NaNoda replay | 10,992 declarations checked with no errors |
| Evidence archive and upload | Success |

All original five targets and all four new endpoints are exported to NaNoda.
The checker is pinned at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, and
lean4export at `6cea97789dc088ea47fcea15692db85685aedac5`. The configuration
rejects every axiom outside the three-item allowlist, including `sorryAx`.
These were hosted-runner checks using downloaded dependencies; an air-gapped
full-library rebuild is not claimed.

The [run snapshot](evidence/run-status.json), [job snapshot](evidence/job-status.json)
and [selected job-log lines](evidence/log-excerpt.txt) preserve compact evidence
in this PR. The negative-control output and full dependency export are in the
workflow artifact; the excerpt is not the complete job log.

## Workflow artifact

[Artifact 10478806837](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300/artifacts/10478806837)
contains tested source, the lockfile, build and checker logs, negative-control
output, a compressed dependency export, checker configuration and checksums.

| Service-reported field | Value |
| --- | --- |
| Name | `jsp-000438-evidence` |
| ZIP size | 8,205,770 bytes |
| ZIP SHA-256 | `19c48bb4eb47984789c486ebf9f9a86c6f75c8d704faf8ca3883af864b69d969` |
| Created | `2026-09-17T03:14:17Z` |
| Reported expiry | `2026-12-16T03:11:18Z` |

These values come from [GitHub artifact metadata](evidence/artifact-metadata.json).
The ZIP digest has not been independently recomputed locally. The external
artifact has finite retention; pinned source and compact receipts remain in
Git, so reviewers can reproduce the checks independently of that artifact.

## Organizer repository checks

The original submission plus this supplement passed schema validation,
Markdown link validation, all 22 repository tests, deterministic data build
and consistency checks, and immutable-history checks against official base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. These are repository-structure
checks and do not determine prize eligibility.
