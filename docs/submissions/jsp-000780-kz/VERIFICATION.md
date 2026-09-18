# Verification

## Completed local checks

On 2026-09-17 UTC, under Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `lake build --wfail`: passed, both project modules (3,094 build jobs).
- Bundled `leanchecker`: passed for `JSP000780` and `Audit`.
- Six named target axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- All nine package revisions match `lake-manifest.json`.
- False arithmetic negative control: rejected, as required.

Exact hashes and outcomes are in `evidence/local-verification.json` and
`evidence/SOURCE_SHA256SUMS`; actual logs are in `evidence/`.
The kernel replay commands are silent on success; their exit codes are recorded.
The quantified proof establishes infinitude; no finite computation is used as
a substitute for that proof.

The local runtime used official cached dependencies and a filesystem readlink
compatibility shim that maps only `/proc/<own PID>/exe` to `/proc/self/exe`.
No Lean kernel, proof or checker code was altered. This is not an offline
full-library rebuild or an independent checker run. The clean hosted run below separately verifies the same proof source.

## Review still needed

Statement fidelity, attribution, prior-work overlap, partial-scope eligibility,
minimum-safe-version approval, human independence and recipient confirmation
remain for the organizers to assess. These are contributor-run checks.
No award decision or permanent external archival is claimed. Workflow artifacts
have finite retention, while source and compact logs are committed to Git.

## Completed hosted and independent checks

[GitHub Actions run 35169276174, attempt 2](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169276174)
completed successfully for proof commit
`d5b210f5507e8a20c401f07e3ebe05209b107bc6`.
The clean runner passed the build, both kernel replays, six axiom audits,
nine revision checks and false-arithmetic control. Strict-allowlist NaNoda
checked **6,049 declarations with no errors**, including the six target
dependency closures. No compiler-trust or native-evaluation axiom was allowed.

`evidence/hosted-verification.json` records the exact run, job, tool pins and
artifact metadata. `evidence/hosted-log-excerpt.txt` retains selected actual
log lines. Attempt 1 failed during installer download; attempt 2 passed all
steps. The first attempt is not claimed as successful proof verification.

Successful artifact: `10476078317`, 3,709,442 bytes. GitHub-reported ZIP
SHA-256: `021c60ce86a4a134eb6d5f4ce642be9fa2b636417dc05cd21b0fd5c9492d0f58`.
[Artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169276174/artifacts/10476078317),
retention expires 2026-12-16. The connector returned archive metadata and a
file URL, but retrieval through that URL returned HTTP 403; a local ZIP rehash
is not claimed. Successful job status and the actual decoded job log were
retrieved. The five proof/configuration files in this submission match the
Git blobs fetched directly from the tested commit.

## Official repository preflight

All 22 repository tests passed, along with `validate`, `links`, `build`,
`check`, and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
Proof-source byte comparison also passed. See `evidence/preflight.json`.
Only this new documentation packet is added. No existing record is changed.
