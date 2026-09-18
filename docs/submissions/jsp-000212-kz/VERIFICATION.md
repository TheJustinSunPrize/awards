# Verification receipt: prime-power modular supplement

## Tested source and observed run

Proof commit: `9ef8a063998150500dcdddad81c669c69ed8fa2c`.

- [Immutable proof project](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/9ef8a063998150500dcdddad81c669c69ed8fa2c/projects/jsp-000212).
- [Workflow at that commit](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9ef8a063998150500dcdddad81c669c69ed8fa2c/.github/workflows/jsp-000212.yml).
- [Successful run 35178083844](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178083844), job `105064125925`, completed 2026-09-17 UTC.
- [Original prime-only verification](INITIAL_VERIFICATION.md).

The four Lean files, build configuration, lockfile, license and verification
scripts match the tested project byte for byte; its README is PROOF.md
here. Submission-facing documents and copied evidence were added afterwards.

| Check | Observed outcome |
| --- | --- |
| Lean 4.34.0 / pinned dependencies | Installed; every dependency revision matched the lockfile |
| Build with warnings as errors | All four modules passed; 3096 jobs |
| Bundled Lean checker replay | BoseChowla, Audit, PrimePower and PrimePowerAudit passed |
| Axiom closures | All ten distinct targets used only propext, Classical.choice and Quot.sound |
| Negative control | Attempted proof of 1 = 0 was rejected |
| Independent NaNoda replay | Checked 24888 declarations with no errors |
| Organizer repository preflight | validate, links, build, check and history passed; all 22 tests passed |

The audit repeats the expanded theorem with its modular predicate unfolded
to equality of remainders and repeats the catalog-facing three-subset type.
Non-prime instances q=4, 8 and 9 retain modular uniqueness and repetitions.
The final theorem constructs the finite-field extension and its dimension.

## Independent checker evidence

The pinned exporter checks out
`6cea97789dc088ea47fcea15692db85685aedac5` (lean4export); the checker checks
out `4c544ed4099c8227f07d5de77ad1e69fb0740a27` (nanoda_lib).
Both old endpoints and both expanded endpoints were exported with their
dependency closures. The strict configuration allows only the three
standard axioms above and treats all unpermitted axioms as hard errors.

The observed checker output was:

```text
2026-09-17T03:27:19.3809511Z Checked 24888 declarations with no errors
```

The decoded public job log is preserved in
[evidence/prime-power-job.log](evidence/prime-power-job.log); only its
leading Unicode byte-order mark was removed. The artifact-list API
response is preserved in
[evidence/prime-power-artifacts.json](evidence/prime-power-artifacts.json).
The initial log and artifact receipt are also retained in evidence/.

## Artifact receipt and limits

- [jsp-000212-evidence artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178083844/artifacts/10479651862).
- ID: `10479651862`.
- GitHub-reported size: `22529489` bytes.
- GitHub-reported ZIP SHA-256: `7ff9777babc4ffa87a06307e09b67943b5dd812030b637d3f7911cc465c03dd1`.
- GitHub-reported expiration: `2026-12-16T03:25:03Z`.

The workflow archives the tested source, lockfile, audit logs, negative
control, kernel logs, NaNoda output and statements, compressed proof export,
configuration and checksums. The ZIP digest was reported by GitHub and
was not independently recomputed from a downloaded ZIP in this session.
Artifacts have finite retention; permanent binary archival is not asserted.
Pinned source and scripts allow regeneration.

This is contributor-run software verification using compiled Mathlib caches.
It does not assert a full source rebuild of Mathlib, independent human
review, designated prize-verifier approval, recipient confirmation or an
award. The finite construction is complete; the original extremal problem
remains unresolved. The extension is a later supplement to one contribution,
and retains the initial source and verification history.
