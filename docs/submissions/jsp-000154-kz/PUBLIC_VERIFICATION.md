# Completed public verification

This report supersedes the initial pending-NaNoda status in the unchanged proof-source VERIFICATION.md. That original file and its checksums are retained for source fidelity.

Proof commit: `96d378d5d0999da2bde29beb1d9f8f7c8ac2dead` in `ketianzhang1-lang/jsp-000301-lean`, directory `projects/jsp-000154`.

[Run 35175990969](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35175990969), job 105057700470, completed successfully on September 17, 2026. Observed results:

- Lean 4.34.0 build with `lake build --wfail`: passed.
- Bundled `leanchecker JSP000154` replay: passed.
- All nine target axiom audits: passed; only `propext`, `Classical.choice`, and `Quot.sound`.
- Every actual dependency Git revision equals its committed lockfile revision.
- The false arithmetic control was rejected.
- Independently implemented NaNoda checked **17,926 declarations with no errors**, covering the nine endpoint dependency closures, with a strict axiom allowlist.

The source and scripts in this submission are byte-identical to the pinned tested package. All 14 original source hashes were checked. The main published source was independently read back through the GitHub connector and matched. The 22 organizer validator tests and validate, links, build, check and history commands passed locally; existing records and generated data are unchanged.

## Artifact and limits

GitHub Actions artifact `10478630598`, `jsp-000154-evidence`, contains the exported proof, checker configuration, logs and tested source archive. GitHub reports 12,831,504 bytes and ZIP SHA-256 `b43bea168061b69a7d0d911e334d6a39a8ae0d793f5669c9e7a613d7358ca5a2`. The advertised expiry is December 16, 2026. These are service-reported metadata; a locally recalculated ZIP digest is not claimed. Permanent independent archival remains pending. Compact actual log excerpts and local receipts are included in the repository.

Checker pins: lean4export `6cea97789dc088ea47fcea15692db85685aedac5`; NaNoda `4c544ed4099c8227f07d5de77ad1e69fb0740a27`. Network access and cached Mathlib were used. These are contributor-run checks with separate checker implementations, not independent human review, organizer acceptance, a current-safe-version determination, or payment authorization. No global priority is claimed.
