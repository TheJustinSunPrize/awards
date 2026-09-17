# Verification receipt

This receipt records contributor-run machine checks, not organizer approval or
independent human review. The mathematical scope is in [STATEMENT.md](STATEMENT.md).

## Immutable source and successful run

- Proof commit: [ba03ade383e1c8dc00008a6200c15232dad43cf9](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/ba03ade383e1c8dc00008a6200c15232dad43cf9/projects/jsp-000017).
- Workflow: [.github/workflows/jsp-000017.yml](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/ba03ade383e1c8dc00008a6200c15232dad43cf9/.github/workflows/jsp-000017.yml).
- Successful run: [35171971482](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171971482).
- Successful job: [105045364631](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171971482/job/105045364631).
- Checks completed on 2026-09-17 UTC, using Lean 4.34.0 and Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

The eight proof-project files here were compared byte-for-byte with the remote
proof commit. Their hashes are in [PROOF_SHA256SUMS](PROOF_SHA256SUMS).

| Check | Observed result |
| --- | --- |
| Lean build, warnings as errors | Success; 3,093 build jobs |
| Bundled Lean checker replay | Success |
| Eight named declaration axiom audits | Only `propext`, `Classical.choice`, `Quot.sound` |
| Actual dependency Git revisions against lockfile | Success |
| False arithmetic negative control (`1 = 0`) | Rejected as required |
| NaNoda, strict axiom allowlist | 13,647 declarations checked with no errors |
| Archive tested source and upload evidence | Success |

The independent checker implementation is NaNoda at
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`, with lean4export at
`6cea97789dc088ea47fcea15692db85685aedac5`. The scripts select all eight named
declarations and their dependencies. The allowlist is exactly the three axioms
above, with a hard error for any other axiom. "Independent" here describes the
checker implementation; all runs were initiated by the contributor.

The compact [public log excerpt](evidence/log-excerpt.txt) and
[job status](evidence/job-status.json) preserve the observed results. The local
[axiom log](evidence/local-axioms.log) is supplementary; the successful remote
run provides the standard reproduction evidence.

## External artifact

[GitHub Actions artifact 10476873166](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171971482/artifacts/10476873166)
contains the source archive, locked manifest, logs, exported dependency closure,
NaNoda configuration, printed statements and internal checksums.

| Field | Recorded value |
| --- | --- |
| Name | `jsp-000017-evidence` |
| ZIP bytes | `8775996` |
| ZIP SHA-256 | `8172795267b73a1adc7e6e12093de4708e8ad17526d1fc9c0264d36e20bcbe71` |
| Created | `2026-09-17T01:51:29Z` |
| Reported expiry | `2026-12-16T01:48:31Z` |

Size and digest agree between the upload log and GitHub's artifact API
([metadata snapshot](evidence/artifact-metadata.json)). They are reported service
values, not a claim of a separately recomputed local ZIP digest. The temporary
artifact download could not be materialized locally (HTTP 403). The Git-pinned
proof source, checked scripts, public run and compact receipts remain available
independently of that temporary transfer.

The artifact has finite retention and is not a permanent archival deposit.
Reviewers should preserve or reproduce it before expiry. Dependency caches and
network access were used; no offline rebuild of the full dependency library is
claimed. The scripts in this directory reproduce the checks.

## Official repository preflight

The repository's 22 unit tests, record validation, local link validation,
deterministic data generation and generated-data consistency checks passed
against official base `f4e7173d89dfe91022a185427d63452c8ffbf6ae` during preparation.
The submitted change is confined to this evidence directory. These checks
validate repository structure; they do not establish award eligibility.
