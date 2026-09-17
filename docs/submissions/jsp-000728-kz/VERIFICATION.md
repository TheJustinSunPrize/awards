# Verification receipt

Proof source: https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0/projects/jsp-000728

Pinned proof commit: `91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0`.

Proof workflow: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171421581

The remote run completed successfully on September 17, 2026. Job 105043714130 passed every step:

- `lake build --wfail`: 3,093 jobs completed successfully.
- Bundled `leanchecker JSP000728`: passed.
- Five target declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- All actual dependency revisions matched the committed manifest.
- False-arithmetic negative control was rejected.
- Pinned NaNoda with a strict allowlist: **4,974 declarations checked, no errors**.

[Compact receipt](evidence/receipt.json) and [exact selected CI log lines](evidence/ci-excerpts.log) preserve the observed evidence. The excerpts omit unrelated dependency-download and build output; they are not represented as a complete job log.

External artifact: `10477250755`, `jsp-000728-evidence`, 3,363,253 bytes. GitHub reports SHA-256 `255250da2ba085a78f391ac46f928cdb8a0856a3bf3e6b00bb8c3a99c5ce0a3d`. Retention expires December 16, 2026 at 01:39:51 UTC. The digest is from the GitHub API; the archive's temporary download URL returned HTTP 403 locally, so an independent local recomputation is not claimed.

All seven proof/configuration/script files in this package were compared byte for byte with the uploaded proof source. The official repository's validate, links, build, check and history commands and all 22 tests passed. [Repository validation log](evidence/repository-validation.log). These structural checks were performed after the source and review documents were assembled; final receipt and checksum additions are checked separately for local links and consistency.

Local checking on September 17, 2026 completed successfully: standard Lean compilation produced an olean, the five declarations in Audit.lean reported only `propext`, `Classical.choice`, and `Quot.sound`, and the bundled `leanchecker JSP000728` exited zero. An existing Mathlib cache at the committed revision was reused. A local process-path compatibility shim redirected only the compiler's own `/proc/<pid>/exe` lookup to `/proc/self/exe`; it did not change Lean source, declarations or checking semantics. Remote CI provides reproduction without that local shim.

## Scope and trust limits

These are contributor-run checks. They do not establish independent human review, organizer certification, global priority, the full original problem, or award eligibility. Cached Mathlib is used; no offline full-library rebuild is claimed. The main theorem has no user-defined research axioms or native-evaluation axiom in its dependency closure.

Full exported proof data belongs in the external workflow artifact. GitHub Actions artifacts have finite retention, so the artifact must be preserved in a permanent archive if required by the organizer. Git-backed source and compact logs do not substitute for a claim of permanent independent archival.
